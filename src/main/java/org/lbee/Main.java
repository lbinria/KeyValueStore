package org.lbee;

import org.lbee.instrumentation.ConfigurationWriter;
import org.lbee.instrumentation.clock.SharedClock;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class Main {
    public static void main(String[] args) throws InterruptedException, IOException {

        // Init shared clock
        //SharedClock.get("kvs").reset();
        // Create a key value store
        final ConsistentStore consistentStore = new ConsistentStore();
        // Configuration
        final Configuration config = new Configuration(8, 8, 8, false);
        ConfigurationWriter.write("kvs.ndjson.conf", config.toHashMap());

        // The set of executing tasks.
        final Collection<Callable<Void>> tasks = new HashSet<>();
        for (int i = 0; i < /* 2 */ 8; i++) {
            final Client c = new Client(consistentStore, config);
            System.out.printf("Create new client %s.\n", c.getGuid());
            tasks.add(c);
        }

        // Run all tasks concurrently.
        final ExecutorService pool = Executors.newCachedThreadPool();
        pool.invokeAll(tasks);

        // This will never be reached.
        pool.shutdown();
        pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
    }
}