import json
import ndjson
from jsonpath import JSONPath
import argparse
import re
import os
import copy

json_conf = dict()

def map_args(name, path, args):
    return [map_val(name, path, val) for val in args]

def map_val(name, path, val):
    if name == "store":
        return val
    elif name == "snapshot":
        return val
    elif name == "transactionPool":
        return val['id']
    elif name == "written" or name == "missed":
        return val

# Overwrite
def map_name(name):
    d = {
        'store': 'store',
        'snapshot': 'snapshotStore',
        'transactionPool': 'tx',
        'written': 'written',
        'missed': 'missed'
    }
    return d[name]

def map_op(name):
    return name


def map_event(event):
    return { 'clock': event['clock'], 'var': map_name(event['var']), 'op': map_op(event['op']), 'path': event['path'], 'args': map_args(event['var'], event['path'], event['args']), 'sender': event['sender'] }

def run(input, configuration):
    global json_conf
    # Open configuration file
    with open(configuration) as f:
        json_conf = ndjson.load(f)[0]

    # Open trace file
    with open(input) as f:
        json_trace = ndjson.load(f)

    json_mapped_trace = list(map(map_event, json_trace))
    return ndjson.dumps(json_mapped_trace)

if __name__ == "__main__":
    # Read program args
    parser = argparse.ArgumentParser(description="")
    parser.add_argument('input', type=str, help="Input (nd)json trace file")
    parser.add_argument('configuration', type=str, help="Configuration (nd)json file")
    args = parser.parse_args()
    # Print output
    print(run(args.input, args.configuration))
