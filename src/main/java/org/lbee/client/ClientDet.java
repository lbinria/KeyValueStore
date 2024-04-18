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
import org.lbee.store.TransactionException;
import org.lbee.store.ValueExistsException;

/**
 * Key value store consumer
 */
public class ClientDet implements Callable<Boolean> {
    // Client guid
    private final int guid;
    // Store used by client
    private final Store store;
    // potential keys and values
    List<Integer> keys;
    List<String> values;
    // Random used to make some stochastic behavior
    private final Random random;
    private static int nbc = 0;

    public ClientDet(Store store, List<Integer> keys, List<String> values) throws IOException {
        this.guid = nbc++;
        this.store = store;
        this.keys = keys;
        this.values = values;
        this.random = new Random();
    }

    @Override
    public Boolean call() throws InterruptedException {
        boolean commitSucceed = false;
        // long startTime = System.currentTimeMillis();

        for(int nbt = 0; nbt < 5; nbt++) {
            // open a new transaction
            Transaction tx = null;
            try {
                tx = store.open();
            } catch (IOException e) {
                e.printStackTrace();
                return false;
            } catch (TransactionException e) {
                System.out.printf("--- No more transaction for client %s.\n", guid);
                return false;
            }
            System.out.printf("-- Open a new transaction %s from client %s.\n", tx, guid);

            // Do some update, read, delete
            int nRequest = 5;
            System.out.printf("Making %s request for %s.\n", nRequest, tx);
            for (int i = 0; i < nRequest; i++) {
                this.doSomething(tx);
                // Simulate some delay
                TimeUnit.MILLISECONDS.sleep(10);
            }
            System.out.printf("Done with requests for %s.\n", tx);

            // Try to commit
            try {
                commitSucceed = store.close(tx);
            } catch (IOException e) {
                e.printStackTrace();
            }
            if (commitSucceed) {
                System.out.printf("--- Commit transaction %s from client %s.\n", tx, guid);
            } else {
                System.out.printf("xxx Abort transaction %s from client %s.\n", tx, guid);
            }

            // Wait some delay before opening a new transaction
            TimeUnit.SECONDS.sleep(1);
            // stop after some time
            // if (System.currentTimeMillis() - startTime >= 5 * 1000)
            //     break;
        }
        return commitSucceed;
    }

    private void doSomething(Transaction tx) {
        // pick an action for read, add, replace, remove
        final int actionNumber = random.nextInt(0, 99);
        // Choose a random key from the list of keys
        Integer key = keys.get(random.nextInt(0, keys.size()));

        // Read: 20% chance
        if (actionNumber <= 19) {
            store.read(key);
        }
        // Add or replace: 75% chance
        else if (actionNumber <= 95) {
            // Choose a value randomly
            String val = values.get(random.nextInt(0, values.size()));
            try {
                store.update(tx, key, val);
            } catch (KeyNotExistsException | ValueExistsException e) {
                System.out.println("*** Key " + key + " doesn't exist or already the same valule");
            } catch (IOException e) {
                System.out.println("Tracing error");
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
