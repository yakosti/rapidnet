## -*- Mode: python; py-indent-offset: 4; indent-tabs-mode: nil; coding: utf-8; -*-

def build(bld):
    module = bld.create_ns3_module('sdn-mac-learning', ['internet-stack'])
    module.source = [
        'sdn-mac-learning.cc',
        ]
    headers = bld.new_task_gen('ns3header')
    headers.module = 'sdn-mac-learning'
    headers.source = [
        'sdn-mac-learning.h',
        'sdn-mac-learning-helper.h',
        ]
