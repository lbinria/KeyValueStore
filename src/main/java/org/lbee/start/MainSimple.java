package org.lbee.start;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.lbee.client.ClientSimple;
import org.lbee.store.KeyExistsException;
import org.lbee.store.Store;

public class MainSimple {
    public static void main(String[] args) throws InterruptedException, IOException, KeyExistsException {
        Store store = new Store();

        final Collection<Callable<Boolean>> tasks = new HashSet<>();

        final ClientSimple c1 = new ClientSimple(store);
        final ClientSimple c2 = new ClientSimple(store);
        final ClientSimple c3 = new ClientSimple(store);

        // Run all tasks concurrently.
        final ExecutorService pool = Executors.newCachedThreadPool();
        tasks.add(c1);
        Collection<Future<Boolean>> future = pool.invokeAll(tasks);

        tasks.remove(c1);
        tasks.add(c2);
        tasks.add(c3);

        future = pool.invokeAll(tasks);
        for (Future<Boolean> f : future) {
            // Boolean result = null;
            try {
                f.get();
            } catch (InterruptedException | ExecutionException e) {
                e.printStackTrace();
            }
        }

        pool.shutdown();
        // pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);

        System.out.println(store);
    }

}