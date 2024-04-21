### Commands

#### BFS (for 10 keys, 20 values)
`KeyValueStore/spec > TRACE_PATH=../BenchMarks/trace.ndjson.4C.VEA CONFIG_PATH=../BenchMarks/conf.10-20-5.ndjson java -XX:+UseParallelGC -cp '/Users/cirstea/bin/TLA/tla2tools.jar' tlc2.TLC -note  KeyValueStoreTrace.tla`

#### DFS (for 10 keys, 20 values)
`KeyValueStore/spec > TRACE_PATH=../BenchMarks/trace.ndjson.4C.VEA CONFIG_PATH=../BenchMarks/conf.10-20-5.ndjson java -XX:+UseParallelGC -Dtlc2.tool.queue.IStateQueue=StateDeque  -cp '/Users/cirstea/bin/TLA/tla2tools.jar' tlc2.TLC -note  KeyValueStoreTrace.tla`

### Benchmarks

#### 4 agents - 10 keys, 20 values, 10 transactions
- trace.ndjson.4C.VEA (120 states)
- trace.ndjson.4Ca.VEA (111 states)
#### 8 agents - 10 keys, 20 values, 10 transactions 
- trace.ndjson.8C.VEA (245 states (VpEA )
- trace.ndjson.8Cb.VEA (247 states, VpEA 6916 states)
- trace.ndjson.8Ca.VpEA (155 states, VpEA 5950 states)
#### 12 agents - 10 keys, 20 values, 10 transactions 
- trace.ndjson.12C.VEA (280 states, VpEA 6916 states)

#### 4 agents - 20 keys, 40 values, 10 transactions
- trace.ndjson.4C-2.VEA ( states)
#### 8 agents - 20 keys, 40 values, 10 transactions
- trace.ndjson.8C-2.VEA ( states)
#### 12 agents - 20 keys, 40 values, 10 transactions
- trace.ndjson.12C-2.VEA ( states)

#### invalid trace 12 agents - 10 keys, 20 values, 10 transactions 
- trace.ndjson.BUG-12.VEA ( states)
