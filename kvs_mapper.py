import json
import ndjson
from jsonpath import JSONPath
import argparse
import re
import os
from dict_recursive_update import recursive_update
import copy

# Open configuration file
with open("kvs.ndjson.conf") as f:
    json_conf = ndjson.load(f)[0]

# print(json_conf)

def identity(val): return val
def null(): return "null"

def default_val(name):
    if name == 'store':
        return {key : null() for key in json_conf['Key']}
    elif name == 'snapshot':
        return {txId : {key : null() for key in json_conf['Key']} for txId in json_conf['TxId']}
    elif name == 'transactionPool':
        return []
    elif name == 'writtenLog' or name == 'missedLog':
        return {txId : [] for txId in json_conf['TxId']}

# def map_val(name, ctx, val):
#     if name == "store":
#         return default_val(name) | val
#     elif name == "snapshot":
#         new_val = {ctx[0]: val}
#         return recursive_update(default_val(name), new_val)
#     elif name == "transactionPool":
#         return [x['id'] for x in val]
#     elif name == "writtenLog" or name == "missedLog":
#         new_val = {ctx[0]: val}
#         return default_val(name) | new_val
#         return new_val

def map_val(name, ctx, val):
    if name == "store":
        return val
    elif name == "snapshot":
        return {ctx[0]: val}
    elif name == "transactionPool":
        return [x['id'] for x in val]
    elif name == "writtenLog" or name == "missedLog":
        return {ctx[0]: val}

def map_name(name):
    d = {
        'store': 'store',
        'snapshot': 'snapshotStore',
        'transactionPool': 'tx',
        'writtenLog': 'written',
        'missedLog': 'missed'
    }
    return d[name]

def map_op(name):
    if name == 'set':
        return 'Replace'

# Open trace file
with open("kvs.ndjson") as f:
    json_trace = ndjson.load(f)

variables = dict()

def map_merge_val(name, ctx, val):
    global variables
    mapped_val = map_val(name, ctx, val)

    if name not in variables:
        variables[name] = default_val(name)

    if type(mapped_val)==dict:
        mapped_val = recursive_update(variables[name], mapped_val)

    variables[name] = mapped_val

    return copy.deepcopy(mapped_val)

def map_event(event):
    return { 'sender': event['sender'], 'var': map_name(event['var']), 'args': map_merge_val(event['var'], event['ctx'], event['args']), 'op': map_op(event['op']), 'clock': event['clock'] }


json_mapped_trace = list(map(map_event, json_trace))
print(ndjson.dumps(json_mapped_trace))
