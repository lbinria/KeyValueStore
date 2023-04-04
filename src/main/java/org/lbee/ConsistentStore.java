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

    private final TraceInstrumentation traceInstrumentation;
    private final TrackedVariable trackedTransactionPool;

    public ConsistentStore(TraceInstrumentation traceInstrumentation) {
        this(new HashMap<>(), traceInstrumentation);
    }

    public ConsistentStore(HashMap<String, String> store, TraceInstrumentation traceInstrumentation) {
        this.store = store;
        this.traceInstrumentation = traceInstrumentation;
        this.transactionPool = new ArrayList<>();
        this.trackedTransactionPool = traceInstrumentation.add("transactionPool", transactionPool);
    }

    public synchronized Transaction open(Client client) {
        Transaction tx = new Transaction(this, client);
        transactionPool.add(tx);
        //trackedTransactionPool.change(transactionPool);

        try {
            trackedTransactionPool.apply("add", tx.getGuid());
//            // End of TLA action Open
            traceInstrumentation.commit();
//            traceInstrumentation.commitChanges();

        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }

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
        // Notify
//        trackedTransactionPool.change(transactionPool);

        try {
            trackedTransactionPool.apply("remove", transaction.getGuid());
            // End of TLA action Close
            traceInstrumentation.commit();
//            traceInstrumentation.commitChanges();
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }
    }

    public void rollback(Transaction transaction) {
        // Just remove transaction from pool without commit
        transactionPool.remove(transaction);
        // Notify
//        trackedTransactionPool.change(transactionPool);

        try {
            trackedTransactionPool.apply("remove", transaction.getGuid());
            // End of TLA action Rollback
            traceInstrumentation.commit();
//            traceInstrumentation.commitChanges();
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
        }
    }

    public long getNbOpenTransaction() {
        return transactionPool.size();
    }

    public ArrayList<Transaction> getTransactionPool() {
        return transactionPool;
    }

    public TraceInstrumentation getTraceInstrumentation() {
        return traceInstrumentation;
    }

    public HashMap<String, String> getStore() {
        return store;
    }

}
