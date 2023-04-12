package org.lbee;

import org.lbee.instrumentation.TraceField;
import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackedVariable;

import java.util.*;

public class Transaction {

    @TraceField(name = "id")
    private final String guid;
    // Written entries log
    private final HashSet<String> writtenLog;

    // Failed ? written entries
    private final HashSet<String> missedLog;

    // Reference store
    private final HashMap<String, String> store;

    /**
     * Snapshot (copy) of reference store
     */
    private final HashMap<String, String> snapshot;

    private final long timeout = -1;

    private final TrackedVariable<HashSet<String>> trackedWrittenLog;
    private final TrackedVariable<HashSet<String>> trackedMissedLog;
    private final TrackedVariable<HashMap<String, String>> trackedSnapshot;
    private final TrackedVariable<HashMap<String, String>> trackedStore;

    public Transaction(ConsistentStore consistentStore, Client client) {
        // Open
        //this.guid = UUID.randomUUID().toString();
        // TODO remove just for test !
        int i = 1;
        String g = "t" + i;

        while (true) {

            boolean found = false;
            for (Transaction tx : client.getStore().getTransactionPool()) {
                if (tx.guid.equals(g)) {
                    found = true;
                    break;
                }
            }
            if (found)
                g = "t" + (++i);
            else
                break;
        }
        this.guid = g;

        this.writtenLog = new HashSet<>();
        this.missedLog = new HashSet<>();
        this.store = consistentStore.getStore();
        this.snapshot = new HashMap<>(store);
        // Note: I have to trace every variable in order to avoid divergences between spec and implementation
        TraceSingleton.getInstance().notifyChange("snapshot", "Init", new String[] { this.guid });
        TraceSingleton.getInstance().notifyChange("snapshot", "UpdateRec", new String[] { this.guid }, snapshot);
//        this.trackedSnapshot.notifyChange(snapshot);

        this.trackedWrittenLog = TraceSingleton.getInstance().add("writtenLog", writtenLog, this.guid);
        this.trackedMissedLog = TraceSingleton.getInstance().add("missedLog", missedLog, this.guid);
        this.trackedSnapshot = TraceSingleton.getInstance().add("snapshot", snapshot, this.guid);
        this.trackedStore = TraceSingleton.getInstance().add("store", store);

    }

    public void addOrReplace(String key, String value) {
        System.out.println("addOrReplace");

        // Note: this condition is imposed by specification
        // Because if we trace trackedSnapshot.apply("add", key, value);
        // There is no action that respond to predicate "This is updated by the same value"
        if (snapshot.containsKey(key) && snapshot.get(key).equals(value))
            return;

        // Change value in snapshot store
        snapshot.put(key, value);
        // Add key in written log
        writtenLog.add(key);

//        trackedSnapshot.notifyChange(snapshot);
//        trackedWrittenLog.notifyChange(writtenLog);

        // Notify modifications
        TraceSingleton.getInstance().notifyChange("snapshot", "Replace",new String[] { this.guid, key }, value);
        TraceSingleton.getInstance().notifyChange("written", "AddElement", new String[] { this.guid }, key);

        TraceSingleton.tryCommit();
    }

    public void remove(String key) {
        System.out.println("remove");

        // Note: Fix made after trace unvalidate because of the following condition of spec:
        // /\ snapshotStore[t][k] /= NoVal (is it necessary ?)
        // But it gave a proof of efficacy for finding bug with trace validation
        if (!snapshot.containsKey(key))
            return;

        snapshot.remove(key);
        writtenLog.add(key);
//        trackedSnapshot.notifyChange(snapshot);
//        trackedWrittenLog.notifyChange(writtenLog);
        TraceSingleton.getInstance().notifyChange("snapshot", "RemoveKey", new String[]{ this.guid }, key);
        TraceSingleton.getInstance().notifyChange("written", "AddElement", new String[]{ this.guid }, key);

        TraceSingleton.tryCommit();
    }

    public void read(String key) {
        snapshot.get(key);
    }

    public void addMissed(HashSet<String> keys) {
        missedLog.addAll(keys);
//        trackedMissedLog.notifyChange(missedLog);
//        TraceSingleton.getInstance().notifyChange("missed", "add_all", new String[]{}, keys);
        for (String key : keys)
            TraceSingleton.getInstance().notifyChange("missed", "AddElement", new String[]{ this.guid }, key);
    }

    /**
     * Check whether transaction can be committed
     * @return True if it can be committed
     */
    public boolean canCommit() {
        return writtenLog.parallelStream().noneMatch(missedLog::contains);
    }

    public HashSet<String> commit() {
        // Close

        // Merging store snapshot into store
        for (String key : writtenLog) {

            if (snapshot.containsKey(key)) {
                String value = snapshot.get(key);
                store.put(key, value);
                TraceSingleton.getInstance().notifyChange("store", "Replace", new String[]{ key }, value);
            }
            else {
                store.remove(key);
                TraceSingleton.getInstance().notifyChange("store", "RemoveKey", new String[]{}, key);
            }
        }
//        trackedStore.notifyChange(store);

        // Copy for return
        final HashSet<String> writtenLogCpy = new HashSet<>(writtenLog);

//        // Clean logs
//        writtenLog.clear();
//        missedLog.clear();
//
////        trackedWrittenLog.notifyChange(writtenLog);
////        trackedMissedLog.notifyChange(missedLog);
//        TraceSingleton.getInstance().notifyChange("written", "Clear", new String[]{ this.guid });
//        TraceSingleton.getInstance().notifyChange("missed", "Clear", new String[]{ this.guid });
//
//
//        // Note: clear snapshot explicitly because it's expected by spec
//        snapshot.clear();
////        trackedSnapshot.notifyChange(snapshot);
//        TraceSingleton.getInstance().notifyChange("snapshot", "ClearRec", new String[]{ this.guid });

        cleanup();

        return writtenLogCpy;
    }

    // Note: I have to add this function just for clear the snapshot...
    public void rollback() {
        cleanup();
//        // Note: clear snapshot explicitly because it's expected by spec
//        snapshot.clear();
////        trackedSnapshot.notifyChange(snapshot);
//        TraceSingleton.getInstance().notifyChange("snapshot", "ClearRec", new String[]{ this.guid });
    }

    private void cleanup() {
        // Note: clear explicitly because it's expected by spec
        writtenLog.clear();
        missedLog.clear();
        snapshot.clear();
        TraceSingleton.getInstance().notifyChange("written", "Clear", new String[]{ this.guid });
        TraceSingleton.getInstance().notifyChange("missed", "Clear", new String[]{ this.guid });
        TraceSingleton.getInstance().notifyChange("snapshot", "Init", new String[]{ this.guid });
    }


    public HashMap<String, String> getSnapshot() {
        return snapshot;
    }

    public String getGuid() { return guid; }
}
