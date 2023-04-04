package org.lbee;

import com.google.gson.JsonElement;
import org.lbee.instrumentation.NDJsonTraceProducer;
import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.TrackedVariable;

import javax.annotation.processing.SupportedSourceVersion;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class Main {
    public static void main(String[] args) throws InterruptedException {

        final TraceInstrumentation traceInstrumentation = new TraceInstrumentation(new NDJsonTraceProducer("kvs.ndjson"), true);
        // Create a key value store
        final ConsistentStore consistentStore = new ConsistentStore(traceInstrumentation);
        // Configuration
        final Configuration config = new Configuration(List.of("k1", "k2", "k3"), List.of("v1", "v2", "v3"), 3);
//        final Configuration config = new Configuration(List.of("k1", "k2", "k3", "k4", "k5", "k6", "k7", "k8"), List.of("v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8"), 8);

        // The set of executing tasks.
        final Collection<Callable<Void>> tasks = new HashSet<>();
        for (int i = 0; i < 2 /* 4 */; i++) {
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