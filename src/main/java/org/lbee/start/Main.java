package org.lbee.start;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import com.google.gson.JsonObject;
import com.google.gson.JsonElement;
import com.google.gson.JsonParser;
import com.google.gson.JsonSyntaxException;
import com.google.gson.Gson;
import com.google.gson.reflect.TypeToken;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.lbee.client.Client;
import org.lbee.store.KeyExistsException;
import org.lbee.store.Store;

public class Main {
    public static void main(String[] args) throws InterruptedException, IOException, KeyExistsException {
        List<String> keys = new ArrayList<>();
        List<String> vals = new ArrayList<>();
        List<String> txIds = new ArrayList<>();
        readConfig("conf.ndjson", keys, vals, txIds);

        Store store = new Store();

        final Collection<Callable<Boolean>> tasks = new HashSet<>();
        for (int i = 0; i < 8; i++) {
            final Client c = new Client(store, keys, vals);
            System.out.printf("Create new client.\n");
            tasks.add(c);
        }

        // Run all tasks concurrently.
        final ExecutorService pool = Executors.newCachedThreadPool();
        Collection<Future<Boolean>> future = pool.invokeAll(tasks);
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

    private static void readConfig(String path, List<String> keys, List<String> values, List<String> txIds) throws IOException {
        try (BufferedReader reader = new BufferedReader(new FileReader(path))) {
            String line = reader.readLine();
            if (line == null) {
                throw new IOException("Configuration file must contains one json object. Invalid configuration file.");
            }
            JsonElement jsonLine = JsonParser.parseString(line);
            if (!jsonLine.isJsonObject()) {
                throw new IOException("Configuration file must contains one json object. Invalid configuration file.");
            }
            JsonObject config = jsonLine.getAsJsonObject();

            Gson gson = new Gson();
            Type listType = new TypeToken<List<String>>() {}.getType();
            List<String> ks = gson.fromJson(config.get("Key").getAsJsonArray(), listType);
            for(String k : ks) {
                keys.add(k);
            }
            List<String> vs = gson.fromJson(config.get("Val").getAsJsonArray(), listType);
            for(String v : vs) {
                values.add(v);
            }
            List<String> txs = gson.fromJson(config.get("TxId").getAsJsonArray(), listType); 
            for(String t : txs) {
                txIds.add(t);
            }
        } catch (JsonSyntaxException e) {
            System.out.println("Invalid json syntax in configuration file.");
        }
    }
}