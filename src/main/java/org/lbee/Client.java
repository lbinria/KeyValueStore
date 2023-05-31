package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.VirtualField;
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

//    private final TraceInstrumentation traceInstrumentation;

    // Store used by client
    private final ConsistentStore store;

    // General configuration
    private final Configuration config;

    // Random used to make some stochastic behavior
    private final Random random;




    public Client(ConsistentStore store, Configuration config) throws IOException {
        this.guid = UUID.randomUUID().toString();
        // One trace instrumentation by client / one clock for app (as algorithm works on the same machine)
//        this.traceInstrumentation = new TraceInstrumentation("kvs_" + guid + ".ndjson", SharedClock.get("kvs.clock"));
        this.store = store;
        this.config = config;
        this.random = new Random();
    }

    @Override
    public Void call() throws Exception {
        long startTime = System.currentTimeMillis();

        while (true) {

            // Check whether we can open a new transaction
            if (store.getNbOpenTransaction() >= config.nbTransactionLimit)
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
        String key = Helpers.pickRandomKey(config);
        // Simulate some delay
        TimeUnit.MILLISECONDS.sleep(random.nextInt(100, 200));

        // Read: 20% chance
        if (actionNumber <= 19) {
            store.read(tx, key);
        }
        // Add or replace: 75% chance
        else if (actionNumber <= 95) {
            // Choose a value randomly
            String val = Helpers.pickRandomVal(config);
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

//    public TraceInstrumentation getTraceInstrumentation() { return traceInstrumentation; }

    public Configuration getConfig() { return config; }

}
