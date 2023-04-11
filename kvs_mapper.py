import json
import ndjson
from jsonpath import JSONPath
import argparse
import re
import os
import copy

# Open configuration file
with open("kvs.ndjson.conf") as f:
    json_conf = ndjson.load(f)[0]

# print(json_conf)
def null(): return "null"

# Overwrite
def default_val(name):
    if name == 'store' or name == 'snapshot':
        return {key : null() for key in json_conf['Key']}
    elif name == 'transactionPool':
        return []
    elif name == 'writtenLog' or name == 'missedLog':
        return {txId : [] for txId in json_conf['TxId']}

def map_args(name, path, args):
    return [map_val(name, path, val) for val in args]

def map_val(name, path, val):
    if not val:
        return default_val(name)
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
    if name == 'set':
        return 'Replace'
    elif name == 'add':
        return 'AddElement'
    elif name == 'add_all':
        return 'AddElements'
    elif name == 'clear':
        return 'Clear'
    elif name == 'clear_record':
        return 'ClearRec'
    elif name == 'remove':
        return 'RemoveElement'
    elif name == 'remove_key':
        return 'RemoveKey'
    elif name == 'update_record':
        return 'UpdateRec'

# Open trace file
with open("kvs.ndjson") as f:
    json_trace = ndjson.load(f)

def map_event(event):
    return { 'clock': event['clock'], 'var': map_name(event['var']), 'op': map_op(event['op']), 'path': event['path'], 'args': map_args(event['var'], event['path'], event['args']), 'sender': event['sender'] }


json_mapped_trace = list(map(map_event, json_trace))
print(ndjson.dumps(json_mapped_trace))
