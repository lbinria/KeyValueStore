package org.lbee.start;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import com.google.gson.JsonObject;
import com.google.gson.JsonElement;
import com.google.gson.JsonParser;
import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.lbee.client.Client;
import org.lbee.client.ClientSimple;
import org.lbee.store.KeyExistsException;
import org.lbee.store.Store;
import org.lbee.store.Transaction;

public class MainSimple {
    public static void main(String[] args) throws InterruptedException, IOException, KeyExistsException {
        List<String> keys = Arrays.asList(new String[] { "K1", "K2" });
        List<String> vals = Arrays.asList(new String[] { "V1", "V2" });

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
            Boolean result = null;
            try {
                result = f.get();
            } catch (InterruptedException | ExecutionException e) {
                e.printStackTrace();
            }
        }

        pool.shutdown();
        // pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);

        System.out.println(store);
    }

}