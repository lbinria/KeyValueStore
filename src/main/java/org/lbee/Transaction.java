package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.VirtualUpdate;

import java.util.HashMap;
import java.util.HashSet;

public class Transaction {

    // Transaction guid
    private final String guid;
    // Written entries log
    private final HashSet<String> writtenLog;
    // Failed written entries
    private final HashSet<String> missedLog;

    private final VirtualField specMissed;
    private final VirtualField specWritten;

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

        this.writtenLog = new HashSet<>();
        this.missedLog = new HashSet<>();

        // Init spec virtual variables
        this.specMissed = consistentStore.specMissed().getField(this.guid);
        this.specWritten = consistentStore.specWritten().getField(this.guid);


        // TLA Note: I have to trace every variable in order to avoid divergences between spec and implementation
        // I use InitWithValue operation, but as variable was clean before, we can use UpdateRec directly
        // We can uncomment lines below, but it's not mandatory (because of clean function)
//        specWritten.init();
//        specMissed.init();
    }

    public void addWritten(String key) {
        // Add key in written log
        writtenLog.add(key);
        specWritten.add(key);
    }

    public void addMissed(HashSet<String> keys) {
        missedLog.addAll(keys);
        // Notify modification
        // Note: We can switch specMissed.addAll and for ... specMissed.add
        // The two are equivalent, we can trace multiple modifications atomically or not
        specMissed.addAll(keys);
        /*
        for (String key : keys)
            specMissed.add(key);
        */
    }

    /**
     * Check whether transaction can be committed
     * @return True if it can be committed
     */
    public boolean canCommit() {
        return writtenLog.parallelStream().noneMatch(missedLog::contains);
    }

    // Note: I have to add this function just for clear the snapshot...
    public void rollback() {
        cleanup();
    }

    public void cleanup() {
        // TLA Note: clear explicitly because it's expected by spec
        writtenLog.clear();
        missedLog.clear();
        specWritten.clear();
        specMissed.clear();
    }

    public String getGuid() { return guid; }

    public HashSet<String> getWrittenLog() {
        return writtenLog;
    }

    public HashSet<String> getMissedLog() {
        return missedLog;
    }
}
