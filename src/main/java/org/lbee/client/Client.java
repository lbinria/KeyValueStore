package org.lbee.client;

import java.io.IOException;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.UUID;
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
public class Client implements Callable<Void> {
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
    public Void call() throws Exception {
        long startTime = System.currentTimeMillis();

        while (true) {
            // open a new transaction
            Transaction tx = store.open();
            System.out.printf("-- Open a new transaction %s from client %s.\n", tx, guid);

            // Do some update, read, delete
            int nRequest = random.nextInt(30);
            System.out.printf("Making %s request for %s.\n", nRequest,tx);
            for (int i = 0; i < nRequest; i++) {
                this.doSomething(tx);
                // Simulate some delay
                TimeUnit.MILLISECONDS.sleep(random.nextInt(100, 200));
            }
            System.out.printf("Done with requests for %s.\n", tx);

            // Try to commit
            boolean commitSucceed = store.close(tx);
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
        return null;
    }

    private void doSomething(Transaction tx) {
        // pick an action for read, add, replace, remove
        final int actionNumber = random.nextInt(0, 99);
        // Choose a random key from the list of keys
        String key = keys.get(random.nextInt(0, keys.size() - 1));

        // Read: 20% chance
        if (actionNumber <= 19) {
            String value = store.read(tx, key);
        }
        // Add or replace: 75% chance
        else if (actionNumber <= 95) {
            // Choose a value randomly
            String val = values.get(random.nextInt(0, values.size() - 1));
            if (actionNumber % 5 == 0) {
                try {
                    store.add(tx, key, val);
                } catch (KeyExistsException e) {
                    System.out.println("*** Key " + key + " already exists");
                }
            } else {
                try {
                    // in most of the cases update an existing key
                    // if (actionNumber % 2 != 0) {
                    Set<String> skeys = store.getKeys();
                    // pick a random key from skeys
                    key = skeys.stream().skip(random.nextInt(skeys.size() - 1)).findFirst().orElse("key");
                    // }
                    store.update(tx, key, val);
                } catch (KeyNotExistsException | ValueExistsException e) {
                    System.out.println("*** Key " + key + " doesn't exist or already the same valule");
                }
            }
        }
        // Remove: 5%
        else {
            try {
                store.remove(tx, key);
            } catch (KeyNotExistsException e) {
                System.out.println("*** Key " + key + " doesn't exist");
            }
        }
    }

}
