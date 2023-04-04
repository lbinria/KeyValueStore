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
    private final TrackedVariable trackedWrittenLog;
    private final TrackedVariable trackedMissedLog;
    private final TrackedVariable trackedSnapshot;
    private final TrackedVariable trackedStore;

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

        snapshot.put(key, value);
        // Add key in written log
        // trackedWrittenLog.before();
        writtenLog.add(key);
        // Notify
//        trackedSnapshot.change(snapshot);
//        trackedWrittenLog.change(writtenLog);
        // TODO make a try apply to avoid try bloc everywhere
        try {
            trackedSnapshot.apply("add", key, value);

            trackedWrittenLog.apply("add", key);
//            // End of the TLA actions Add / Replace
            traceInstrumentation.commit();
//            traceInstrumentation.commitChanges();
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }
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
        // Notify
//        trackedSnapshot.change(snapshot);
//        trackedWrittenLog.change(writtenLog);


        try {
            trackedSnapshot.apply("remove", key);
            trackedWrittenLog.apply("add", key);
//            // End of the TLA actions Remove
            traceInstrumentation.commit();
//            traceInstrumentation.commitChanges();
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }
    }

    public void read(String key) {
        snapshot.get(key);
    }

    public void addMissed(HashSet<String> keys) {
        System.out.println("addMissed");
        missedLog.addAll(keys);
        // Notify
//        trackedMissedLog.change(missedLog);
        try {
            trackedMissedLog.apply("missedUpdate", keys);
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }
    }

    /**
     * Check whether transaction can be committed
     * @return True if it can be committed
     */
    public boolean canCommit() {
        return writtenLog.parallelStream().noneMatch(missedLog::contains);
    }

    public HashSet<String> commit() {
        System.out.println("commit");
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
        // Notify
//        trackedStore.change(store);

        try {
            trackedStore.apply("set", store);
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }

        // Copy for return
        final HashSet<String> writtenLogCpy = (HashSet<String>)writtenLog.clone();

        // Clean logs
        writtenLog.clear();
        missedLog.clear();

        // Notify
//        trackedWrittenLog.change(writtenLog);
//        trackedMissedLog.change(missedLog);

        try {
            trackedWrittenLog.apply("clear");
            trackedMissedLog.apply("clear");
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }

        return writtenLogCpy;
    }

    public HashMap<String, String> getSnapshot() {
        return snapshot;
    }

    public String getGuid() { return guid; }
}
