package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.TraceProducerException;
import org.lbee.instrumentation.TrackedVariable;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class ConsistentStore {

    private final HashMap<String, String> store;
    private final ArrayList<Transaction> transactionPool;

    private final TrackedVariable<ArrayList<Transaction>> trackedTransactionPool;

    public ConsistentStore() {
        this(new HashMap<>());
    }

    public ConsistentStore(HashMap<String, String> store) {
        this.store = store;
        this.transactionPool = new ArrayList<>();
        this.trackedTransactionPool = TraceSingleton.getInstance().add("transactionPool", transactionPool);
    }

    public synchronized Transaction open(Client client) {
        Transaction tx = new Transaction(this, client);
        transactionPool.add(tx);
//        trackedTransactionPool.notifyChange(transactionPool);
        TraceSingleton.getInstance().notifyChange("transactionPool", "AddElement", new String[]{}, tx);

        TraceSingleton.tryCommit();

        return tx;
    }

    /**
     * Try to commit transaction. If some writes was already made by another
     * transaction, rollback.
     * @param transaction Transaction to commit
     */
    public synchronized boolean requestCommit(Transaction transaction) {
        final boolean canCommit = transaction.canCommit();
        // Check whether it can commit
        if (canCommit)
            commit(transaction);
        else
            rollback(transaction);

        return canCommit;
    }

    public void commit(Transaction transaction) {

        // Commit transaction
        HashSet<String> writtenLog = transaction.commit();
        // Add written log as missed for other open transactions
        for (Transaction tx : transactionPool) {
            // Note: bug found here thanks to trace (forget condition)
            if (!tx.equals(transaction))
                tx.addMissed(writtenLog);
        }

        // Remove from pool
        transactionPool.remove(transaction);
//        trackedTransactionPool.notifyChange(transactionPool);
        TraceSingleton.getInstance().notifyChange("transactionPool", "RemoveElement", new String[]{}, transaction);

        TraceSingleton.tryCommit();
    }

    public void rollback(Transaction transaction) {
        // Just remove transaction from pool without commit
        transaction.rollback();
        transactionPool.remove(transaction);
//        trackedTransactionPool.notifyChange(transactionPool);
        TraceSingleton.getInstance().notifyChange("transactionPool", "RemoveElement", new String[]{}, transaction);

        TraceSingleton.tryCommit();
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

}
