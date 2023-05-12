package org.lbee;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.lbee.instrumentation.TraceInstrumentation;

public class ConsistentStore {

    private final HashMap<String, String> store;
    private final ArrayList<Transaction> transactionPool;

    public ConsistentStore() {
        this(new HashMap<>());
    }

    public ConsistentStore(HashMap<String, String> store) {
        this.store = store;
        this.transactionPool = new ArrayList<>();
    }

    public synchronized Transaction open(Client client) {
        Transaction transaction = new Transaction(this, client);

        transactionPool.add(transaction);
        // pourquoi on log ici et pas dans le client? si on le fait par rapport au client (de la transaction)
        // ou plutôt pourquoi ne pas faire TraceInstrumentation[.getInstance()].notifyChange(client,...)
        transaction.getClient().getTraceInstrumentation().notifyChange("tx", "AddElement", new String[]{}, transaction.getGuid());
        transaction.getClient().getTraceInstrumentation().commitChanges("OpenTx");
        return transaction;
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

    // private?
    private void commit(Transaction transaction) {

        // Commit transaction
        HashSet<String> writtenLog = transaction.commit();
        // Remove from pool
        transactionPool.remove(transaction);
        transaction.getClient().getTraceInstrumentation().notifyChange("tx", "RemoveElement", new String[]{}, transaction.getGuid());

        // effet de bord: plus besoin de faire le test (du bug)

        // Add written log as missed for other open transactions
        for (Transaction tx : transactionPool) {
            // Note: bug found here thanks to trace (forget condition)
            if (!tx.equals(transaction)) {
                tx.addMissed(writtenLog);
                // pourquoi faire un log par rapport au client de la tx? ce n'est pas lui le responsable de ce missed
                for (String key : writtenLog)
                    transaction.getClient().getTraceInstrumentation().notifyChange("missed", "AddElement", new String[]{ tx.getGuid() }, key);
                    // TraceInstrumentation.getInstance(ID)....
            }
        }

        // Keep caution to commit at the end
        transaction.getClient().getTraceInstrumentation().commitChanges("CloseTx");
    }

    // private?
    private void rollback(Transaction transaction) {
        // Just remove transaction from pool without commit
        transaction.rollback();
        transactionPool.remove(transaction);

        transaction.getClient().getTraceInstrumentation().notifyChange("tx", "RemoveElement", new String[]{}, transaction.getGuid());
        transaction.getClient().getTraceInstrumentation().commitChanges("RollbackTx");
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
