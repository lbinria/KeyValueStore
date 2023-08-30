package org.lbee;

import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.VirtualUpdate;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public class Transaction {

    // Transaction guid
    private final String guid;

    private final Client client;
    // Written entries log
    private final HashSet<String> writtenLog;
    // Failed written entries
    private final HashSet<String> missedLog;

    private final VirtualField specMissed;
    private final VirtualField specWritten;
    public VirtualField getSpecMissed() { return specMissed; }

    private static String generateGuid(Client client) {
        final Configuration config = client.getStore().getConfig();
        final Set<String> usedTxIds = client.getStore().getTransactionPool().stream().map(Transaction::getGuid).collect(Collectors.toSet());
        final Set<String> allTxIds = new HashSet<>(config.getTxIds());
        // Difference between all tx ids and used tx ids
        allTxIds.removeAll(usedTxIds);
        // Get first (should never crash)
        return allTxIds.stream().findFirst().get();
    }

    public Transaction(ConsistentStore consistentStore, Client client) {
        // Open
        this.guid = generateGuid(client);
        this.client = client;
        this.writtenLog = new HashSet<>();
        this.missedLog = new HashSet<>();

        // Init spec virtual variables
        this.specMissed = client.getSpecMissed().getField(this.guid);
        this.specWritten = client.getSpecWritten().getField(this.guid);


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

    public void addMissed(Client client, HashSet<String> keys) {
        missedLog.addAll(keys);
        // Notify modification
        // Note: We can switch specMissed.addAll and for ... specMissed.add
        // The two are equivalent, we can trace multiple modifications atomically or not
        client.getSpecMissed().getField(this.guid).addAll(keys);
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

    public Client getClient() { return client; }
}
