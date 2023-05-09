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

    private final Client client;

    private final long timeout = -1;


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
        this.client = client;

        this.writtenLog = new HashSet<>();
        this.missedLog = new HashSet<>();
        this.store = consistentStore.getStore();
        this.snapshot = new HashMap<>(store);
        // TLA Note: I have to trace every variable in order to avoid divergences between spec and implementation
        // I use InitWithValue operation, but as variable was clean before, we can use UpdateRec directly
        client.getTraceInstrumentation().notifyChange("snapshotStore", "InitWithValue", new String[] { this.guid }, snapshot);
        // We can uncomment lines below, but it's not mandatory (because of clean function)
//        client.getTraceInstrumentation().notifyChange("written", "Init", new String[]{ this.guid });
//        client.getTraceInstrumentation().notifyChange("missed", "Init", new String[]{ this.guid });


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

        // Notify modifications
        client.getTraceInstrumentation().notifyChange("snapshotStore", "Replace",new String[] { this.guid, key }, value);
        client.getTraceInstrumentation().notifyChange("written", "AddElement", new String[] { this.guid }, key);

        client.getTraceInstrumentation().commitChanges("AddOrReplace");
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

        client.getTraceInstrumentation().notifyChange("snapshotStore", "RemoveKey", new String[]{ this.guid }, key);
        client.getTraceInstrumentation().notifyChange("written", "AddElement", new String[]{ this.guid }, key);

        client.getTraceInstrumentation().commitChanges("Remove");
    }

    public void read(String key) {
        snapshot.get(key);
    }

    public void addMissed(HashSet<String> keys) {
        missedLog.addAll(keys);
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
                client.getTraceInstrumentation().notifyChange("store", "Replace", new String[]{ key }, value);
            }
            else {
                store.remove(key);
                client.getTraceInstrumentation().notifyChange("store", "RemoveKey", new String[]{}, key);
            }
        }
//        trackedStore.notifyChange(store);

        // Copy for return
        final HashSet<String> writtenLogCpy = new HashSet<>(writtenLog);

        cleanup();

        return writtenLogCpy;
    }

    // Note: I have to add this function just for clear the snapshot...
    public void rollback() {
        cleanup();
    }

    private void cleanup() {
        // TLA Note: clear explicitly because it's expected by spec
        writtenLog.clear();
        missedLog.clear();
        snapshot.clear();
        client.getTraceInstrumentation().notifyChange("written", "Clear", new String[]{ this.guid });
        client.getTraceInstrumentation().notifyChange("missed", "Clear", new String[]{ this.guid });
        client.getTraceInstrumentation().notifyChange("snapshotStore", "Init", new String[]{ this.guid });
    }

    public HashMap<String, String> getSnapshot() {
        return snapshot;
    }

    public String getGuid() { return guid; }

    public Client getClient() { return client; }
}
