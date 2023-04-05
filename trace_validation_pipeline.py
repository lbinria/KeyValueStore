
import os
import time
import signal
from subprocess import Popen, PIPE

print("# Clean up")

trace_files = [f for f in os.listdir(".") if f.endswith('.ndjson')]
print(f"Cleanup: {trace_files}")
for trace_file in trace_files:
    os.remove(trace_file)

print("# Start implementation.\n")

impl_process = Popen([
    "python",
    "run_impl.py"
])

# Wait all client are finished
impl_process.wait()
impl_process.terminate()

print("# Convert traces for TLA+.\n")

merge_process = Popen([
    "python",
    "/home/me/Projects/trace_validation_tools/tools/tla_trace_converter_pipeline.py",
    "--files",
    ".",
    "--map",
    "kvs.map.json",
#     "--validate"
], stdout=PIPE)

merge_process.wait()
merge_process.terminate()

# merged_events = merge_process.stdout.read().decode('utf-8')
# with open("trace-merged.ndjson", "w") as f:
#     f.write(merged_events)

print("# Start TLA+ trace spec.\n")

tla_trace_validation_process = Popen([
    "python",
    "/home/me/Projects/trace_validation_tools/tools/tla_trace_validation.py",
    "spec/KeyValueStoreTrace.tla",
    "trace-tla.ndjson"])

tla_trace_validation_process.wait()

print("End pipeline.")