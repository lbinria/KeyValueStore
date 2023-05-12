package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.LogicalClock;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public class ConsistentStore implements KeyValueStoreSpec {

    private final HashMap<String, String> store;
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

    public synchronized Transaction open(Client client) {
        Transaction transaction = new Transaction(this, client);

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
        specTx.remove(transaction.getGuid());

        // effet de bord: plus besoin de faire le test (du bug)

        // Add written log as missed for other open transactions
        for (Transaction tx : transactionPool) {
            // Note: bug found here thanks to trace (forget condition)
            if (!tx.equals(transaction)) {
                tx.addMissed(writtenLog);
            }
        }

        // Keep caution to commit at the end
        spec.commitChanges("CloseTx");
    }

    // private?
    private void rollback(Transaction transaction) {
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

    public VirtualField getSpecStore() {
        return specStore;
    }
}
