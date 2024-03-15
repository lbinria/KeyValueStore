package org.lbee.client;

import java.io.IOException;
import java.util.List;
import java.util.Random;
import java.util.concurrent.Callable;
import java.util.concurrent.TimeUnit;

import org.lbee.store.KeyExistsException;
import org.lbee.store.KeyNotExistsException;
import org.lbee.store.Store;
import org.lbee.store.Transaction;
import org.lbee.store.ValueExistsException;

/**
 * Key value store consumer
 */
public class Client implements Callable<Boolean> {
    // Client guid
    private final int guid;
    // Store used by client
    private final Store store;
    // potential keys and values
    List<String> keys;
    List<String> values;
    // Random used to make some stochastic behavior
    private final Random random;
    private static int nbc = 0;

    public Client(Store store, List<String> keys, List<String> values) throws IOException {
        this.guid = nbc++;
        this.store = store;
        this.keys = keys;
        this.values = values;
        this.random = new Random();
    }

    @Override
    public Boolean call() throws Exception {
        boolean commitSucceed = false;
        long startTime = System.currentTimeMillis();

        while (true) {
            // open a new transaction
            Transaction tx = store.open();
            System.out.printf("-- Open a new transaction %s from client %s.\n", tx, guid);

            // Do some update, read, delete
            int nRequest = random.nextInt(10);
            System.out.printf("Making %s request for %s.\n", nRequest,tx);
            for (int i = 0; i < nRequest; i++) {
                this.doSomething(tx);
                // Simulate some delay
                TimeUnit.MILLISECONDS.sleep(random.nextInt(100, 200));
            }
            System.out.printf("Done with requests for %s.\n", tx);

            // Try to commit
            commitSucceed = store.close(tx);
            if (commitSucceed) {
                System.out.printf("--- Commit transaction %s from client %s.\n", tx, guid);
            } else {
                System.out.printf("xxx Abort transaction %s from client %s.\n", tx, guid);
            }

            // Wait some delay before opening a new transaction
            TimeUnit.SECONDS.sleep(random.nextInt(2, 6));
            // stop after some time
            if (System.currentTimeMillis() - startTime >= 15 * 1000)
                break;
        }
        return commitSucceed;
    }

    private void doSomething(Transaction tx) {
        // pick an action for read, add, replace, remove
        final int actionNumber = random.nextInt(0, 99);
        // Choose a random key from the list of keys
        String key = keys.get(random.nextInt(0, keys.size()));

        // Read: 20% chance
        if (actionNumber <= 19) {
            store.read(key);
        }
        // Add or replace: 75% chance
        else if (actionNumber <= 95) {
            // Choose a value randomly
            String val = values.get(random.nextInt(0, values.size()));
            if (actionNumber % 5 != 0) {
                try {
                    store.add(tx, key, val);
                } catch (KeyExistsException e) {
                    System.out.println("*** Key " + key + " already exists");
                } catch (IOException e) {
                    System.out.println("Tracing error");
                }
            } else {
                try {
                    store.update(tx, key, val);
                } catch (KeyNotExistsException | ValueExistsException e) {
                    System.out.println("*** Key " + key + " doesn't exist or already the same valule");
                } catch (IOException e) {
                    System.out.println("Tracing error");
                }
            }
        }
        // Remove: 5%
        else {
            try {
                store.remove(tx, key);
            } catch (KeyNotExistsException e) {
                System.out.println("*** Key " + key + " doesn't exist");
            } catch (IOException e) {
                System.out.println("Tracing error");
            }
        }
    }

}
