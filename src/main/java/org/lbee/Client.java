package org.lbee;

import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;
import org.lbee.instrumentation.clock.ClockFactory;
import org.lbee.instrumentation.clock.SharedClock;

import java.io.IOException;
import java.util.Random;
import java.util.UUID;
import java.util.concurrent.Callable;
import java.util.concurrent.TimeUnit;

/**
 * Key value store consumer
 */
public class Client implements Callable<Void> {

    // Client guid
    private final String guid;

    // Store used by client
    private final ConsistentStore store;

    // Random used to make some stochastic behavior
    private final Random random;

    private final BehaviorRecorder spec;
    private final VirtualField specTx;
    private final VirtualField specStore;
    private final VirtualField specMissed;
    private final VirtualField specWritten;
    private final VirtualField specSnapshotStore;


    public Client(ConsistentStore store) throws IOException {
        this.guid = UUID.randomUUID().toString();
        this.store = store;
        this.random = new Random();

        spec = BehaviorRecorder.create("kvs_" + guid + ".ndjson", SharedClock.get("kvs.clock"));
        // Init spec virtual variables
        this.specTx = spec.getVariable("tx");
        this.specStore = spec.getVariable("store");
        this.specMissed = spec.getVariable("missed");
        this.specWritten = spec.getVariable("written");
        this.specSnapshotStore = spec.getVariable("snapshotStore");
    }

    public BehaviorRecorder getSpec() { return spec; }
    public VirtualField getSpecTx() { return specTx; }
    public VirtualField getSpecStore() { return specStore; }
    public VirtualField getSpecMissed() { return specMissed; }
    public VirtualField getSpecWritten() { return specWritten; }
    public VirtualField getSpecSnapshotStore() { return specSnapshotStore; }

    @Override
    public Void call() throws Exception {
        long startTime = System.currentTimeMillis();

        while (true) {

            // Check whether we can open a new transaction
            if (store.getNbOpenTransaction() >= store.getConfig().nbTransactionLimit)
                continue;



            // Open a transaction
            Transaction tx = store.open(this);
            System.out.printf("Open a new transaction %s from client %s.\n", tx.getGuid(), guid);

            // Do some update, read, delete
            int nRequest = random.nextInt(20);
            System.out.printf("Make %s request.\n", nRequest);
            for (int i = 0; i < nRequest; i++)
                doSomething(tx);

            // Try to commit
            boolean commitSucceed = store.requestCommit(tx);
            System.out.printf("Commit a transaction %s from client %s : %s.\n", tx.getGuid(), guid, commitSucceed);

            // Wait some delay before opening a new transaction
            TimeUnit.SECONDS.sleep(random.nextInt(2, 6));

            if (System.currentTimeMillis()-startTime >= 15 * 1000)
                break;
        }

        return null;
    }

    private void doSomething(Transaction tx) throws InterruptedException {
        final int actionNumber = random.nextInt(0, 99);

        // Choose a key randomly
        String key = Helpers.pickRandomKey(store.getConfig());
        // Simulate some delay
        TimeUnit.MILLISECONDS.sleep(random.nextInt(100, 200));

        // Read: 20% chance
        if (actionNumber <= 19) {
            store.read(tx, key);
        }
        // Add or replace: 75% chance
        else if (actionNumber <= 95) {
            // Choose a value randomly
            String val = Helpers.pickRandomVal(store.getConfig());
            store.addOrReplace(tx, key, val);
        }
        // Remove: 5%
        else {
            store.remove(tx, key);
        }
    }

    public String getGuid() { return guid; }

    public ConsistentStore getStore() {
        return store;
    }

    public void tryCommitChanges(String eventName) {
        try {
            spec.commitChanges(eventName);
        } catch (IOException e) {
            try {
                spec.commitException("commit failed.");
            } catch (IOException ex) {
                throw new RuntimeException(ex);
            }
        }
    }

}
