package org.lbee.client;

import java.io.IOException;
import java.util.concurrent.Callable;
import java.util.concurrent.TimeUnit;

import javax.management.openmbean.KeyAlreadyExistsException;

import org.lbee.store.KeyExistsException;
import org.lbee.store.KeyNotExistsException;
import org.lbee.store.Store;
import org.lbee.store.Transaction;
import org.lbee.store.TransactionException;
import org.lbee.store.ValueExistsException;

/**
 * Key value store consumer
 */
public class ClientSimple implements Callable<Boolean> {
    // Client guid
    private final int guid;
    // Store used by client
    private Store store;
    private static int nbc = 0;

    public ClientSimple(Store store) throws IOException {
        this.guid = nbc++;
        this.store = store;
    }

    @Override
    public Boolean call() throws InterruptedException {
        boolean commitSucceed = false;

        Transaction tx = null;
        try {
            tx = store.open();
        } catch (IOException e) {
            e.printStackTrace();
            return false;
        } catch (TransactionException e) {
            System.out.printf("--- No more transaction for client %s.\n", guid);
            // e.printStackTrace();
            return false;
        }

        if (guid == 0) {
            try {
                store.add(tx, "K1", "V1");
                store.add(tx, "K2", "V2");
            } catch (KeyExistsException | IOException e) {
                e.printStackTrace();
            }
        } else {
            TimeUnit.SECONDS.sleep(2);
            String v1 = store.read("K1");
            String v2 = store.read("K2");
            try {
                store.add(tx, "K1" + guid, "V1" + guid);
                if (guid == 1) {
                    store.update(tx, "K1", v1 + "-1");
                } else {
                    store.update(tx, "K2", v2 + "-2");
                }
                TimeUnit.MILLISECONDS.sleep(100);
                if (guid == 2) {
                    store.update(tx, "K1", v1 + "-2");
                } else {
                    store.update(tx, "K2", v2 + "-1");
                }
            } catch (KeyExistsException | KeyNotExistsException | ValueExistsException | IOException | InterruptedException e) {
                e.printStackTrace();
            }

            TimeUnit.SECONDS.sleep(2);
        }

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

        return commitSucceed;
    }

}
