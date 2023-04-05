package org.lbee;

import org.lbee.instrumentation.TraceField;
import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackedVariable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

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

    private final TraceInstrumentation traceInstrumentation;
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

        this.traceInstrumentation = consistentStore.getTraceInstrumentation();
        this.trackedWrittenLog = this.traceInstrumentation.add("writtenLog", writtenLog, this.guid);
        this.trackedMissedLog = this.traceInstrumentation.add("missedLog", missedLog, this.guid);
        this.trackedSnapshot = this.traceInstrumentation.add("snapshot", snapshot, this.guid);
        this.trackedStore = this.traceInstrumentation.add("store", store);
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
        trackedSnapshot.notifyChange(snapshot);
        // Add key in written log
        writtenLog.add(key);
        trackedWrittenLog.notifyChange(writtenLog);

        Helpers.tryCommit(traceInstrumentation);
    }

    public void remove(String key) {
        System.out.println("remove");

        // Note: Fix made after trace unvalidate because of the following condition of spec:
        // /\ snapshotStore[t][k] /= NoVal (is it necessary ?)
        // But it gave a proof of efficacy for finding bug with trace validation
        if (!snapshot.containsKey(key))
            return;

        snapshot.remove(key);
        trackedSnapshot.notifyChange(snapshot);
        writtenLog.add(key);
        trackedWrittenLog.notifyChange(writtenLog);

        Helpers.tryCommit(traceInstrumentation);
    }

    public void read(String key) {
        snapshot.get(key);
    }

    public void addMissed(HashSet<String> keys) {
        missedLog.addAll(keys);
        trackedMissedLog.notifyChange(missedLog);
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
            }
            else
                store.remove(key);

        }
        trackedStore.notifyChange(store);

        // Copy for return
        final HashSet<String> writtenLogCpy = new HashSet<>(writtenLog);

        // Clean logs
        writtenLog.clear();
        missedLog.clear();

        trackedWrittenLog.notifyChange(writtenLog);
        trackedMissedLog.notifyChange(missedLog);

        return writtenLogCpy;
    }

    public HashMap<String, String> getSnapshot() {
        return snapshot;
    }

    public String getGuid() { return guid; }
}
