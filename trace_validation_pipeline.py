import os
import time
import signal
from subprocess import Popen, PIPE
import run_impl
import kvs_mapper
from trace_validation_tools import tla_trace_converter

print("# Clean up")

trace_files = [f for f in os.listdir(".") if f.endswith('.ndjson')]
print(f"Cleanup: {trace_files}")
for trace_file in trace_files:
    os.remove(trace_file)

print("# Start implementation.\n")

run_impl.run()

print("# Map traces.\n")

trace_mapped = kvs_mapper.run("kvs.ndjson", "kvs.ndjson.conf")
# Write to file
with open("trace-mapped.ndjson", "w") as f:
    f.write(trace_mapped)

print("# Convert traces for TLA+.\n")

trace_tla = tla_trace_converter.run("trace-mapped.ndjson", "kvs.ndjson.conf")
# Write to file
with open("trace-tla.ndjson", "w") as f:
    f.write(trace_tla)

print("# Start TLA+ trace spec.\n")


tla_trace_validation_process = Popen([
    "python",
    "/home/me/Projects/trace_validation_tools/tools/tla_trace_validation.py",
    "spec/KeyValueStoreTrace.tla",
    "trace-tla.ndjson"])

tla_trace_validation_process.wait()

print("End pipeline.")