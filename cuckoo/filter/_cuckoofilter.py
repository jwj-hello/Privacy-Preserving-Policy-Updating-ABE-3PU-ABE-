"""
Cuckoo Filter
"""

import random

from . import bucket
from . import exceptions
from . import hashutils
from . import hiddenitem


class CuckooFilter(object):
    """
    Cuckoo Filter class.

    Implements insert, delete and contains operations for the filter.
    """

    def __init__(self, capacity, bucket_size=4, fingerprint_size=1,
                 max_displacements=500):
        """
        Initialize CuckooFilter object.

        :param capacity: Size of the Cuckoo Filter
        :param bucket_size: Number of entries in a bucket
        :param fingerprint_size: Fingerprint size in bytes
        :param max_displacements: Maximum number of evictions before filter is
        considered full
        """
        self.capacity = capacity
        self.bucket_size = bucket_size
        self.fingerprint_size = fingerprint_size
        self.max_displacements = max_displacements
        self.buckets = [bucket.Bucket(size=bucket_size)
                        for _ in range(self.capacity)]
        self.size = 0

    def __repr__(self):
        return '<CuckooFilter: capacity=' + str(self.capacity) + \
               ', size=' + str(self.size) + ', fingerprint size=' + \
               str(self.fingerprint_size) + ' byte(s)>'

    def __len__(self):
        return self.size

    def __contains__(self, item):
        return self.contains(item)

    def _get_index(self, item):
        index = hashutils.hash_code(item) % self.capacity
        return index

    def _get_alternate_index(self, index, fingerprint):
        alt_index = (index ^ hashutils.hash_code(fingerprint)) % self.capacity
        return alt_index

    def insert(self, item):
        """
        Insert an item into the filter.

        :param item: Item to be inserted.
        :return: True if insert is successful; CuckooFilterFullException if
        filter is full.
        """
        fingerprint = hashutils.fingerprint(item, self.fingerprint_size)
        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)

        if self.buckets[i].insert(fingerprint) \
                or self.buckets[j].insert(fingerprint):
            self.size += 1
            return True

        eviction_index = random.choice([i, j])
        for _ in range(self.max_displacements):
            f = self.buckets[eviction_index].swap(fingerprint)
            eviction_index = self._get_alternate_index(eviction_index, f)
            if self.buckets[eviction_index].insert(f):
                self.size += 1
                return True
        # Filter is full
        raise exceptions.CuckooFilterFullException('Insert operation failed. '
                                                   'Filter is full.')

    def modified_insert(self, item):
        """
        Insert an item into the filter.

        :param item: Item to be inserted.
        :return: 1 if without relocating process or 0 if with relocating process
        """
        fingerprint = hashutils.fingerprint(item, self.fingerprint_size)
        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)
        if self.buckets[i].insert(fingerprint) \
                or self.buckets[j].insert(fingerprint):
            self.size += 1
            return 1
        # Necessary for inserting the fingerprint into the next cuckoo filter
        return 0

    def modified_insert_addXorValue(self, item, value):
        """
        Insert an item into the filter.

        :param item: Item to be inserted.
        :return: 1 if without relocating process or 0 if with relocating process
        """
        fingerprint = hashutils.fingerprint(item, self.fingerprint_size)
        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)
        composite = hiddenitem.HiddenItem(fingerprint,value)
        if self.buckets[i].insert(composite) \
                or self.buckets[j].insert(composite) :
            self.size += 1
            return 1
        # Necessary for inserting the fingerprint into the next cuckoo filter
        return 0

    def insert(self, item):
        """
        Insert an item into the filter.

        :param item: Item to be inserted.
        :return: True if insert is successful; CuckooFilterFullException if
        filter is full.
        """
        fingerprint = hashutils.fingerprint(item, self.fingerprint_size)
        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)

        if self.buckets[i].insert(fingerprint) \
                or self.buckets[j].insert(fingerprint):
            self.size += 1
            return True

        eviction_index = random.choice([i, j])
        for _ in range(self.max_displacements):
            f = self.buckets[eviction_index].swap(fingerprint)
            eviction_index = self._get_alternate_index(eviction_index, f)
            if self.buckets[eviction_index].insert(f):
                self.size += 1
                return True
        # Filter is full
        raise exceptions.CuckooFilterFullException('Insert operation failed. '
                                                   'Filter is full.')


    def contains(self, item):
        """
        Check if the filter contains the item.

        :param item: Item to check its presence in the filter.
        :return: True, if item is in the filter; False, otherwise.
        """
        fingerprint = hashutils.fingerprint(item, self.fingerprint_size)

        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)

        return fingerprint in self.buckets[i] or fingerprint in self.buckets[j]

    def modified_contains(self, item):
        """
        Check if the filter contains the item.

        :param item: Item to check its presence in the filter.
        :return: True, if item is in the filter; False, otherwise.
        """
        fingerprint = hashutils.fingerprint(item, self.fingerprint_size)

        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)

        # return fingerprint in self.buckets[i].bucket or fingerprint in self.buckets[j].bucket
        for ele in self.buckets[i].bucket+self.buckets[j].bucket:
            if fingerprint in ele:
                return True
        return False

    def getHiddenItem(self,item):
        """
        get HiddenItem object according to item
        :param item: Item to check its presence in the filter.
        :return: HiddenItem object.
        """

        fingerprint = hashutils.fingerprint(item, self.fingerprint_size)

        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)

        # return fingerprint in self.buckets[i].bucket or fingerprint in self.buckets[j].bucket
        for ele in self.buckets[i].bucket + self.buckets[j].bucket:
            if fingerprint in ele:
                return ele
        return None

    def delete(self, item):
        """
        Delete an item from the filter.

        To delete an item safely, it must have been previously inserted.
        Otherwise, deleting a non-inserted item might unintentionally remove
        a real, different item that happens to share the same fingerprint.

        :param item: Item to delete from the filter.
        :return: True, if item is found and deleted; False, otherwise.
        """
        fingerprint = hashutils.fingerprint(item, size=self.fingerprint_size)
        i = self._get_index(item)
        j = self._get_alternate_index(i, fingerprint)
        if self.buckets[i].delete(fingerprint) \
                or self.buckets[j].delete(fingerprint):
            self.size -= 1
            return True
        return False

    ''' Insert algorithm which can avoid collision with existed entry in the buckets '''

def antiCollisionInsert(cfList=[], index=0, item='', value=0):
    if cfList[index].modified_insert_addXorValue(item, value) == 1:
        # print('insert into the first filter directly')
        return 1
    # print('insert into the following filter')
    return antiCollisionInsert(cfList, index + 1, item, value)

def antiCollisionFind(cfList=[], item=''):
    for i in range(len(cfList)):
        if cfList[i].modified_contains(item):
            return True
    return False