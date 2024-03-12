package org.lbee.client;

import java.io.IOException;
import java.util.concurrent.Callable;
import java.util.concurrent.TimeUnit;

import org.lbee.store.Store;
import org.lbee.store.Transaction;

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
    public Boolean call() throws Exception {
        boolean commitSucceed = false;

        Transaction tx = store.open();

        if (guid == 0) {
            store.add(tx, "K1", "V1");
            store.add(tx, "K2", "V2");
        } else {
            TimeUnit.SECONDS.sleep(2);
            String v1 = store.read("K1");
            String v2 = store.read("K2");
            if (guid == 1) {
                store.add(tx, "K1", v1+"-1");
            } else {
                store.add(tx, "K2", v2+"-2");
            }
            TimeUnit.MILLISECONDS.sleep(100);
            if (guid == 2) {
                store.add(tx, "K1", v1+"-2");
            } else {
                store.add(tx, "K2", v2+"-1");
            }
            TimeUnit.SECONDS.sleep(2);
        }

        commitSucceed = store.close(tx);
        if (commitSucceed) {
            System.out.printf("--- Commit transaction %s from client %s.\n", tx, guid);
        } else {
            System.out.printf("xxx Abort transaction %s from client %s.\n", tx, guid);
        }

        return commitSucceed;
    }

}
