"""
存放fingerprint,fingerprint xor value
"""

class HiddenItem(object):
    def __init__(self,fingerprint,value):
        self.fingerprint = fingerprint
        self.xor_value = value ^ fingerprint

    def __repr__(self):
        return '<Item: ' + str(self.fingerprint) + ',' + ',' + str(self.xor_value) + '>'

    def __contains__(self, item):
        return item == self.fingerprint

    def get_content(self):
        return self.fingerprint, self.xor_value
