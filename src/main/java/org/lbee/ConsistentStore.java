package org.lbee;

import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.ClockFactory;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class ConsistentStore /*implements KeyValueStoreSpec*/ {

    private final HashMap<String, String> store;
    private final Configuration config;
    /**
     * Snapshot (copy) of reference store
     */
    private final HashMap<String, HashMap<String, String>> snapshots;
    private final ArrayList<Transaction> transactionPool;

    public ConsistentStore(Configuration config) {
        this(new HashMap<>(), config);
    }

    public ConsistentStore(HashMap<String, String> store, Configuration config) {
        this.store = store;
        this.config = config;
        this.snapshots = new HashMap<>();
        this.transactionPool = new ArrayList<>();
    }

    private void makeSnapshot(Transaction t) {
        // Copy store to snapshot
        this.snapshots.put(t.getGuid(), new HashMap<>(store));
        // Notify modification
        t.getClient().getSpecSnapshotStore().getField(t.getGuid()).init(store);;
    }

    public void addOrReplace(Transaction transaction, String key, String value) {
        System.out.println("addOrReplace");

        final HashMap<String, String> snapshot = snapshots.get(transaction.getGuid());
        // Note: this condition is imposed by specification
        // Because if we trace trackedSnapshot.apply("add", key, value);
        // There is no action that respond to predicate "This is updated by the same value"
        if (snapshot.containsKey(key) && snapshot.get(key).equals(value))
            return;

        // Check if it is an Add or Update action
        final String eventName;
        if (snapshot.containsKey(key))
            eventName = "Update";
        else
            eventName = "Add";

        // Change value in snapshot store
        snapshot.put(key, value);
        // Notify modifications
        transaction.getClient().getSpecSnapshotStore().getField(transaction.getGuid()).getField(key).set(value);

        // Add key in written log
        transaction.addWritten(key);

        transaction.getClient().tryCommitChanges(eventName);
    }

    public void remove(Transaction transaction, String key) {
        System.out.println("remove");

        final HashMap<String, String> snapshot = snapshots.get(transaction.getGuid());

        // Note: Fix made after trace unvalidate because of the following condition of spec:
        // /\ snapshotStore[t][k] /= NoVal (is it necessary ?)
        // But it gave a proof of efficacy for finding bug with trace validation
        if (!snapshot.containsKey(key))
            return;

        snapshot.remove(key);
        // Notify modifications
        transaction.getClient().getSpecSnapshotStore().getField(transaction.getGuid()).removeKey(key);

        // Add key in written log
        transaction.addWritten(key);

        transaction.getClient().tryCommitChanges("Remove");
    }

    public void read(Transaction transaction, String key) {
        final HashMap<String, String> snapshot = snapshots.get(transaction.getGuid());
        snapshot.get(key);
    }

    public synchronized Transaction open(Client client) {
        Transaction transaction = new Transaction(this, client);
        makeSnapshot(transaction);

        transactionPool.add(transaction);
        client.getSpecTx().add(transaction.getGuid());
        client.tryCommitChanges("OpenTx");
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

    /* Add synchronized because we make a modification on global variable transaction pool */
    /* Two client doesn't do modification on this global variable at the same time */
    private synchronized void commit(Transaction transaction) {

        // Commit transaction
        HashSet<String> writtenLog = flush(transaction);

        // Remove from pool
        transactionPool.remove(transaction);
        transaction.getClient().getSpecTx().remove(transaction.getGuid());

        // Add written log as missed for other open transactions
        for (Transaction tx : transactionPool) {
            tx.addMissed(transaction.getClient(), writtenLog);
        }

        // Keep caution to commit at the end
        transaction.getClient().tryCommitChanges("CloseTx");
    }

    public HashSet<String> flush(Transaction tx) {
        // Close
        final HashMap<String, String> snapshot = snapshots.get(tx.getGuid());

        // Merging store snapshot into store
        for (String key : tx.getWrittenLog()) {

            if (snapshot.containsKey(key)) {
                String value = snapshot.get(key);
                store.put(key, value);
                tx.getClient().getSpecStore().getField(key).set(value);
            }
            else {
                store.remove(key);
                tx.getClient().getSpecStore().removeKey(key);
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

        transaction.getClient().getSpecTx().remove(transaction.getGuid());
        transaction.getClient().tryCommitChanges("RollbackTx");
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

    public Configuration getConfig() { return config; }
}
