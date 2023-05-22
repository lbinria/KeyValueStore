package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.LogicalClock;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class ConsistentStore implements KeyValueStoreSpec {

    private final HashMap<String, String> store;
    /**
     * Snapshot (copy) of reference store
     */
    private final HashMap<String, HashMap<String, String>> snapshots;
    private final ArrayList<Transaction> transactionPool;

    private final TraceInstrumentation spec;

    private final VirtualField specTx;
    private final VirtualField specStore;
    private final VirtualField specMissed;
    private final VirtualField specWritten;
    private final VirtualField specSnapshotStore;

    public TraceInstrumentation spec() { return spec; }
    public VirtualField specTx() { return specTx; }
    public VirtualField specStore() { return specStore; }
    public VirtualField specMissed() { return specMissed; }
    public VirtualField specWritten() { return specWritten; }
    public VirtualField specSnapshotStore() { return specSnapshotStore; }

    public ConsistentStore() {
        this(new HashMap<>());
    }



    public ConsistentStore(HashMap<String, String> store) {
        this.store = store;
        this.snapshots = new HashMap<>();
        this.transactionPool = new ArrayList<>();

        // TODO create trace instrumentation here ! Should remove client because it's not in spec !
        spec = new TraceInstrumentation("kvs.ndjson", new LogicalClock());
        // SpecBehavior consistentStoreBehavior.
        // Init spec virtual variables
        this.specTx = spec.getVariable("tx");
        this.specStore = spec.getVariable("store");
        this.specMissed = spec.getVariable("missed");
        this.specWritten = spec.getVariable("written");
        this.specSnapshotStore = spec.getVariable("snapshotStore");
    }

    private void makeSnapshot(Transaction t) {
        // Copy store to snapshot
        this.snapshots.put(t.getGuid(), new HashMap<>(store));
        // Notify modification
        specSnapshotStore.getField(t.getGuid()).init(store);;
    }

    public synchronized void addOrReplace(Transaction transaction, String key, String value) {
        System.out.println("addOrReplace");

        final HashMap<String, String> snapshot = snapshots.get(transaction.getGuid());
        // Note: this condition is imposed by specification
        // Because if we trace trackedSnapshot.apply("add", key, value);
        // There is no action that respond to predicate "This is updated by the same value"
        if (snapshot.containsKey(key) && snapshot.get(key).equals(value))
            return;

        // Change value in snapshot store
        snapshot.put(key, value);
        // Notify modifications
        specSnapshotStore.getField(transaction.getGuid()).getField(key).set(value);

        // Add key in written log
        transaction.addWritten(key);

        spec.commitChanges("AddOrReplace");
    }

    public synchronized void remove(Transaction transaction, String key) {
        System.out.println("remove");

        final HashMap<String, String> snapshot = snapshots.get(transaction.getGuid());

        // Note: Fix made after trace unvalidate because of the following condition of spec:
        // /\ snapshotStore[t][k] /= NoVal (is it necessary ?)
        // But it gave a proof of efficacy for finding bug with trace validation
        if (!snapshot.containsKey(key))
            return;

        snapshot.remove(key);
        // Notify modifications
        specSnapshotStore.getField(transaction.getGuid()).removeKey(key);

        // Add key in written log
        transaction.addWritten(key);

        spec.commitChanges("Remove");
    }

    public void read(Transaction transaction, String key) {
        final HashMap<String, String> snapshot = snapshots.get(transaction.getGuid());
        snapshot.get(key);
    }

    public synchronized Transaction open(Client client) {
        Transaction transaction = new Transaction(this, client);
        makeSnapshot(transaction);

        transactionPool.add(transaction);
        // pourquoi on log ici et pas dans le client? si on le fait par rapport au client (de la transaction)
        // ou plutôt pourquoi ne pas faire TraceInstrumentation[.getInstance()].notifyChange(client,...)
        specTx.add(transaction.getGuid());
        spec.commitChanges("OpenTx");
        return transaction;
    }

    /**
     * Try to commit transaction. If some writes was already made by another
     * transaction, rollback.
     * @param transaction Transaction to commit
     */
    public boolean requestCommit(Transaction transaction) {
        final boolean canCommit = transaction.canCommit();
        // Check whether it can commit
        if (canCommit)
            commit(transaction);
        else
            rollback(transaction);

        return canCommit;
    }

    private synchronized void commit(Transaction transaction) {

        // Commit transaction
        HashSet<String> writtenLog = flush(transaction);

        // Remove from pool
        transactionPool.remove(transaction);
        specTx.remove(transaction.getGuid());

        // Add written log as missed for other open transactions
        for (Transaction tx : transactionPool) {
            // Note: bug found here thanks to trace (forget condition)
                tx.addMissed(writtenLog);
        }

        // Keep caution to commit at the end
        spec.commitChanges("CloseTx");
    }

    public HashSet<String> flush(Transaction tx) {
        // Close
        final HashMap<String, String> snapshot = snapshots.get(tx.getGuid());

        // Merging store snapshot into store
        for (String key : tx.getWrittenLog()) {

            if (snapshot.containsKey(key)) {
                String value = snapshot.get(key);
                store.put(key, value);
                specStore.getField(key).set(value);
            }
            else {
                store.remove(key);
                specStore.removeKey(key);
            }
        }

        final HashSet<String> written = new HashSet<>(tx.getWrittenLog());
        tx.cleanup();

        return written;
    }

    private synchronized void rollback(Transaction transaction) {
        // Just remove transaction from pool without commit
        transaction.rollback();
        transactionPool.remove(transaction);

//        transaction.getClient().getTraceInstrumentation().notifyChange("tx", "RemoveElement", new String[]{}, transaction.getGuid());
        specTx.remove(transaction.getGuid());
        spec.commitChanges("RollbackTx");
    }

    public long getNbOpenTransaction() {
        return transactionPool.size();
    }

    public ArrayList<Transaction> getTransactionPool() {
        return transactionPool;
    }

    public HashMap<String, String> getStore() {
        return store;
    }

    public TraceInstrumentation getSpec() { return spec; }

}
