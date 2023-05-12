package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.VirtualUpdate;

import java.util.HashMap;
import java.util.HashSet;

public class Transaction {

    private final String guid;
    // Written entries log
    private final HashSet<String> writtenLog;
    // Failed written entries
    private final HashSet<String> missedLog;

    // Reference store
    private final HashMap<String, String> store;

    /**
     * Snapshot (copy) of reference store
     */
    private final HashMap<String, String> snapshot;

    private final Client client;

    private final TraceInstrumentation spec;
    private final VirtualField specMissed;
    private final VirtualField specWritten;
    private final VirtualField specSnapshotStore;
    private final VirtualField specStore;

    // utiliser le suivant modulo nbMax?
    private static String generateGuid(Client client) {
        while (true) {
            // Pick up random tx id
            String txId = Helpers.pickRandomTxId(client.getConfig());
            // If no open transaction has this id we keep it
            if (client.getStore().getTransactionPool().stream().noneMatch(t -> t.getGuid().equals(txId)))
                return txId;
        }
    }

    public Transaction(ConsistentStore consistentStore, Client client) {
        // Open
        this.guid = generateGuid(client);
        this.client = client;

        this.writtenLog = new HashSet<>();
        this.missedLog = new HashSet<>();
        this.store = consistentStore.getStore();
        this.snapshot = new HashMap<>(store);

        // Init spec virtual variables
        this.spec = consistentStore.getSpec();
//        this.specMissed = consistentStore.getSpec().getVariable("missed").getField(this.guid);
//        this.specWritten = consistentStore.getSpec().getVariable("written").getField(this.guid);
//        this.specSnapshotStore = consistentStore.getSpec().getVariable("snapshotStore").getField(this.guid);
//        this.specStore = consistentStore.getSpecStore();
        this.specMissed = consistentStore.specMissed().getField(this.guid);
        this.specWritten = consistentStore.specWritten().getField(this.guid);
        this.specSnapshotStore = consistentStore.specSnapshotStore().getField(this.guid);
        this.specStore = consistentStore.getSpecStore();


        // TLA Note: I have to trace every variable in order to avoid divergences between spec and implementation
        // I use InitWithValue operation, but as variable was clean before, we can use UpdateRec directly
        specSnapshotStore.init(snapshot);
        // We can uncomment lines below, but it's not mandatory (because of clean function)
//        specWritten.init();
//        specMissed.init();
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
        specSnapshotStore.getField(key).set(value);
        specWritten.add(key);

        spec.commitChanges("AddOrReplace");
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

        specSnapshotStore.removeKey(key);
        specWritten.add(key);

        spec.commitChanges("Remove");
    }

    public void read(String key) {
        snapshot.get(key);
    }

    public void addMissed(HashSet<String> keys) {
        missedLog.addAll(keys);
        // TODO test with AddElements (just showing that atomic addAll is equivalent to add in loop)
        for (String key : writtenLog)
            specMissed.add(key);
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
//                client.getTraceInstrumentation().notifyChange("store", "Replace", new String[]{ key }, value);
                specStore.getField(key).set(value);
            }
            else {
                store.remove(key);
//                client.getTraceInstrumentation().notifyChange("store", "RemoveKey", new String[]{}, key);
                specStore.removeKey(key);
            }
        }

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
        specWritten.clear();
        specMissed.clear();
        specSnapshotStore.init();
    }

    public String getGuid() { return guid; }

    public Client getClient() { return client; }

    public VirtualField getSpecMissed() {
        return specMissed;
    }
}
