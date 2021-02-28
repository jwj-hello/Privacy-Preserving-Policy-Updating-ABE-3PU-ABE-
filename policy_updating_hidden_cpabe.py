"""
Zuobin Ying, Wenjie Jiang

| From: "Reliable Policy Updating under Efficient Policy-Hidden Fine-grained Access Control Framework in
the Cloud"
| Security Assumption: Decisional Parallel Bilinear Diffie-Hellman Exponent
|
| type:           ciphertext-policy attribute-based encryption with policy-hiding and policy-updating
| setting:        Pairing

:Authors:         Wenjie Jiang
:Date:            02/2021
"""

from charm.toolbox.ABEnc import ABEnc
from charm.toolbox.msp import MSP
from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, G2, GT, pair
import random
import itertools
import cuckoofilter
import hashutils
import copy
import time
debug = False


class Waters11(ABEnc):

    def __init__(self, group_obj, uni_size, verbose=False):
        ABEnc.__init__(self)
        self.group = group_obj
        self.uni_size = uni_size  # bound on the size of the universe of attributes
        self.util = MSP(self.group, verbose)
        self.maxSpaceUsage = 0.5
        self.bucketSize = 4
        self.capacity = 25
        self.fingerprint_size = 8
        self.maxCFNumber = 20
        self.default = 1

    def setup(self):
        """
        Generates public key and master secret key.
        """

        if debug:
            print('Setup algorithm:\n')

        # pick a random element each from two source groups and pair them
        g1 = self.group.random(G1)
        g2 = self.group.random(G2)
        alpha = self.group.random(ZR)
        g1_alpha = g1 ** alpha
        e_gg_alpha = pair(g1_alpha, g2)
        e_gg_alpha_for_acf = pair(g1_alpha, g1)  # generate for encrypt which is used in acf
        a = self.group.random(ZR)
        g1_a = g1 ** a

        h = [0]
        for i in range(self.uni_size):
            h.append(self.group.random(G1))

        pk = {'g1': g1, 'g2': g2, 'g1_a': g1_a, 'h': h, 'e_gg_alpha': e_gg_alpha,
              'e_gg_alpha_for_acf': e_gg_alpha_for_acf}
        msk = {'g1_alpha': g1_alpha}
        return pk, msk

    def keygen(self, pk, msk, attr_list):
        """
        Generate a key for a set of attributes.
        """

        if debug:
            print('Key generation algorithm:\n')
        # key for cp_abe
        t = self.group.random(ZR)
        k0 = msk['g1_alpha'] * (pk['g1_a'] ** t)
        L = pk['g2'] ** t
        K = {}
        for attr in attr_list:
            K[attr] = pk['h'][int(attr)] ** t

        # key for acf_encrypt
        m = self.group.random(ZR)
        K3 = msk['g1_alpha'] * ((pk['g1_a']) ** m)
        K4 = pk['g1'] ** m

        key_for_cpabe = {'attr_list': attr_list, 'k0': k0, 'L': L, 'K': K}
        key_for_acf = {'K3': K3, 'K4': K4}
        return {'KEY_CP_ABE': key_for_cpabe, 'KEY_ACF': key_for_acf}

    def access_structure_create(self, MSP_ACCESS):
        """
        this part is seted for generating the access matrix and rho
        """

        _msp_access = copy.deepcopy(MSP_ACCESS)  # this is necessary becase the characteristic of dictionary in python
        access_matrix = {}
        rho = {}
        # generate the access matrix and rho
        for i in range(1, len(_msp_access) + 1):
            attr = random.sample(_msp_access.keys(), 1)  # this step make rho to be different in every process
            access_matrix[i] = _msp_access[attr[0]]  # put the selected attribute into matrix
            rho[attr[0]] = i  # put the mapping relation into rho
            del _msp_access[attr[0]]
        return {'access_matrix': access_matrix, 'rho': rho}

    def acf_encrypt(self, pk):
        """
        this part is set to encrypt the m_for_acf which is used for xor with the attr_row_str
        """

        n = self.group.random(ZR)
        C_FOR_ACF = pk['e_gg_alpha_for_acf'] ** n
        C3 = pk['g1'] ** n
        C4 = pk['g1_a'] ** n
        return {'C3': C3, 'C4': C4, 'C_FOR_ACF': C_FOR_ACF}

    def acf_create(self, rho, c_for_acf):
        """
        this part is set to generate the cuckoofilter which is used for save the encrypted mapping relation
        """

        cfList = [cuckoofilter.CuckooFilter(self.capacity, self.bucketSize, self.fingerprint_size)
                  for i in range(self.maxCFNumber)]  # initialize the cuckoofilter
        # this part is used for inserting the mapping relation into the cuckoofilter
        for attr, row in rho.items():
            # translate the attr and row to the int, because the next step:'{:032b}'.format(x) request a int input
            attr_str = int(attr)
            row_str = int(row)
            attr_str = '{:032b}'.format(attr_str)  # set the attr_str'length as 32
            row_str = '{:032b}'.format(row_str)  # set the row_str'length as 32
            attr_row_str = attr_str + row_str  # splice attr_str and row_str together
            value_for_xor = ""  # initialize the value_for_xor which is used for saving the result
            # xor the m_for_xor with the attr_row_str
            for i in range(len(c_for_acf)):
                bit = int(list(c_for_acf)[i]) ^ int(list(attr_row_str)[i])
                value_for_xor += str(bit)
            # after xor wo put the result which is value_for_xor into the cuckoofilter
            fingerprint = hashutils.fingerprint(attr, self.fingerprint_size)
            cuckoofilter.new_antiCollisionInsert(cfList=cfList, fingerprint=fingerprint, value=value_for_xor)
        return cfList

    def encrypt(self, pk, msg, policy_str):
        """
        this part is set to encrypt the plaintext and generate the ciphertext
        """

        # the list u[] is used for saving n random numbers, the first ele of u[] is the secret s which we use in LSSS
        # n is the length of access_matrix's row
        u = []
        if debug:
            print('Encryption algorithm:\n')
        #  the m_for_acf_encrypt will be used in acf_encrypt as the m_for_acf
        # m_for_acf_encrypt = self.group.random(GT)
        #  encrypt the m_for_acf by acf_encrypt
        cipher_for_acf = self.acf_encrypt(pk)
        C3 = cipher_for_acf['C3']
        C4 = cipher_for_acf['C4']
        C_FOR_ACF = cipher_for_acf['C_FOR_ACF']

        policy = self.util.createPolicy(policy_str)
        mono_span_prog = self.util.convert_policy_to_msp(policy)
        num_cols = self.util.len_longest_row  # num_cols represent the length of access_matrix's row

        #  generate access structure(access_matrix, rho)
        access_structure = self.access_structure_create(mono_span_prog)
        #  before xor the m_for_acf and the attr_row_str, translate the m_for_acf_encrypt into string by hash function
        c_for_acf = str(C_FOR_ACF)
        c_for_acf = hashutils.fingerprint(c_for_acf, 64)
        c_for_acf = '{:064b}'.format(c_for_acf)
        #  generate cuckoo_filter by acf_create
        cflist = self.acf_create(access_structure['rho'], c_for_acf)
        # pick randomness
        for i in range(num_cols):
            rand = self.group.random(ZR)
            u.append(rand)
        s = u[0]  # the secret s which is going to be shared
        c0 = pk['g2'] ** s
        dic_for_secret = {}
        # encrypt the message by cp-abe scheme
        C = {}
        C_FOR_UPLOAD = {}
        D = {}
        D_FOR_UPLOAD = {}
        for attr, row in mono_span_prog.items():
            cols = len(row)
            sum = 0
            for i in range(cols):
                sum += row[i] * u[i]
            attr_stripped = self.util.strip_index(attr)
            r_attr = self.group.random(ZR)
            c_attr = (pk['g1_a'] ** sum) / (pk['h'][int(attr_stripped)] ** r_attr)
            d_attr = pk['g2'] ** r_attr
            C[attr] = c_attr
            D[attr] = d_attr
            # this step is hidden the attributes in C[] and D[], change them into the C_FOR_UPLOAD and D_FOR_UPLOAD
            if attr in access_structure['rho'].keys():
                row_in_rho = access_structure['rho'][attr]
                C_FOR_UPLOAD[row_in_rho] = C[attr]
                D_FOR_UPLOAD[row_in_rho] = D[attr]
            # dic_as is used for saving the current secret share value
            dic_for_secret[attr] = sum
        c_m = (pk['e_gg_alpha'] ** s) * msg
        # cipher_for_upload will be uploaded to the cloud
        cipher_for_upload = {'c0': c0, 'C_FOR_UPLOAD': C_FOR_UPLOAD, 'D_FOR_UPLOAD': D_FOR_UPLOAD, 'c_m': c_m, 'C3': C3,
                             'C4': C4, 'access_matrix': access_structure['access_matrix'],
                             'ACF': cflist}
        # cipher_for_local will be saved in local for policy update
        cipher_for_local = {'MSP': mono_span_prog, 'RHO': access_structure['rho'], 'NUM_COLS': num_cols,
                            'DIC_FOR_SECRET': dic_for_secret, 'U': u, 'C_FOR_ACF': c_for_acf}

        return {'C_U': cipher_for_upload, 'C_L': cipher_for_local}

    def upload_request(self, upload_ctxt, update_ctxt):
        """
        this part is set to simulate the cloud services
        """

        # cloud_ctxt is set as the ciphertext which is going to send to decryption algorithm
        if upload_ctxt is not None and update_ctxt is None:
            cloud_ciphertext = upload_ctxt
            return cloud_ciphertext
        if upload_ctxt is not None and update_ctxt is not None:
            cloud_ciphertext = upload_ctxt
            c_for_upload = cloud_ciphertext['C_FOR_UPLOAD']
            d_for_upload = cloud_ciphertext['D_FOR_UPLOAD']
            access_matrix = cloud_ciphertext['access_matrix']
            acf = cloud_ciphertext['ACF']
            uc_for_cipher = update_ctxt['UC_FOR_CIPHER']
            uc_for_access_structure = update_ctxt['UC_FOR_ACCESS_STRUCTURE']
            for key, value in uc_for_cipher.items():
                if key in c_for_upload.keys():
                    if value[0] == 'alter':
                        c_for_upload[key] *= value[1]
                    if value[0] == 'delete':
                        del c_for_upload[key]
                        del d_for_upload[key]
                else:
                    if value[0] == 'insert':
                        c_for_upload[key] = value[1]
                        d_for_upload[key] = value[2]
            for key, value in uc_for_access_structure.items():
                if key in access_matrix.keys():
                    if value[0] == 'alter':
                        access_matrix[key] = value[1]
                    if value[0] == 'delete':
                        # delete the vector of access_matrix which is related with key
                        del access_matrix[key]
                        # delete the components of acf which is related with fingerprint
                        cuckoofilter.new_antidelete(cfList=acf, fingerprint=value[1])

                else:
                    if value[0] == 'insert':
                        access_matrix[key] = value[1]
                        cuckoofilter.new_antiCollisionInsert(cfList=acf, fingerprint=value[2], value=value[3])
            return cloud_ciphertext

    def acf_decrypt(self, cloud_ctxt, key):
        """
        this part is set to decrypt the C_FOR_ACF
        """

        C3 = cloud_ctxt['C3']
        C4 = cloud_ctxt['C4']
        K3 = key['KEY_ACF']['K3']
        K4 = key['KEY_ACF']['K4']
        c_for_acf = pair(C3, K3) / pair(C4, K4)
        # before using the m_for_acf, we will perform some translation just like we did in encrypt
        c_for_acf = str(c_for_acf)
        c_for_acf = hashutils.fingerprint(c_for_acf, 64)
        c_for_acf = '{:064b}'.format(c_for_acf)
        return c_for_acf

    def acf_prune(self, cloud_ctxt, attr_list, c_for_acf):
        """
        this part is set to prune the attr_list with the rho
        """

        acf_prune_list = {}  # initialize the acf_prune_list
        cflist = cloud_ctxt['ACF']  # get the cuckoofilter from the cloud ctxt
        for attr in attr_list:
            attr = str(attr)
            fingerprint = hashutils.fingerprint(attr, self.fingerprint_size)
            if cuckoofilter.new_antiCollisionFind(cflist, fingerprint):
                _value = cuckoofilter.new_antigetHiddenItem(cflist, fingerprint)
                _value = _value.value
                attr_str = ''
                row_str = ''
                for i in range(len(c_for_acf)):
                    bit = int(list(c_for_acf)[i]) ^ int(list(_value)[i])
                    if i <= 31:
                        attr_str += str(bit)
                    if i >= 32:
                        row_str += str(bit)
                attr_str = str(int(attr_str, 2))  # convert binary string attr_str to string
                row_str = int(row_str, 2)  # convert binary string row_str to int
                acf_prune_list[attr_str] = row_str  # recover the part related to attr_list in rho
        return acf_prune_list

    def access_matrix_prune(self, acf_prune_list, cloud_ctxt):
        """
        this part is set to prune the matrix with the attr_prune_list to get the prune_list which satisfy access policy
        """

        access_matrix = cloud_ctxt['access_matrix']  # get the access_matrix from the cloud_ctxt
        access_matrix_for_prune = {}  # initialize the access_matrix_for_prune
        len_max = 0
        compare_v = []
        # recover the part which relate to attr_list in access_matrix as the access_matrix_for_prune
        for attr, row in acf_prune_list.items():
            access_matrix_for_prune[attr] = access_matrix[row]
        # compute the len_max of vectors for attribute
        for attr, value in access_matrix_for_prune.items():
            if len_max < len(value):
                len_max = len(value)
        # initialize the vector (1,0,0,0,...,0)
        for i in range(0, len_max):
            if i == 0:
                compare_v.insert(i, 1)
            else:
                compare_v.insert(i, 0)
        # confirm that there is a minimum attribute set that satisfies the access policy in the acf_prune_list
        for i in range(1, len(access_matrix_for_prune) + 1):
            for j in itertools.combinations(access_matrix_for_prune.keys(), i):  # the function combinations for attr
                sum_v = access_matrix_for_prune[j[0]]
                # add the vectors to find the pruned attr_list
                for k in range(1, i):
                    # add two lists together
                    sum_v = list(map(lambda x: x[0] + x[1], zip(sum_v, access_matrix_for_prune[j[k]])))
                if len_max > len(sum_v):
                    for l in range(len(sum_v), len_max):
                        sum_v.insert(l, 0)
                if sum_v == compare_v:
                    prune_list = list(j)
                    return prune_list  # find the pruned attr_list
        return None  # don't find the pruned attr_list

    def decrypt(self, pk, cloud_ctxt, key):
        """
        this part is set to prune the matrix with the attr_prune_list to get the prune_list which satisfy policy
        """
        if debug:
            print('Decryption algorithm:\n')
        # compute the c_for_acf by acf_decrypt
        c_for_acf = self.acf_decrypt(cloud_ctxt, key)
        # get the user's attr_list form the key
        attr_list = key['KEY_CP_ABE']['attr_list']
        # compute the acf_prune_list by acf_prune
        acf_prune_list = self.acf_prune(cloud_ctxt, attr_list, c_for_acf)
        # compute the prune_list by access_matrix_prune
        prune_list = self.access_matrix_prune(acf_prune_list, cloud_ctxt)
        # determine whether the user's attributes satisfy the policy.
        if prune_list is None:
            print("Policy not satisfied.")
            return None
        # if user's attributes satisfy the policy, we perform the decryption
        prodG = 1
        prodGT = 1
        key = key['KEY_CP_ABE']  # get the user's key from the key

        for i in range(0, len(prune_list)):
            attr = prune_list[i]
            row = acf_prune_list[attr]
            attr_stripped = self.util.strip_index(attr)
            prodG *= cloud_ctxt['C_FOR_UPLOAD'][row]
            prodGT *= pair(key['K'][attr_stripped], cloud_ctxt['D_FOR_UPLOAD'][row])

        return (cloud_ctxt['c_m'] * pair(prodG, key['L']) * prodGT) / (pair(key['k0'], cloud_ctxt['c0']))

    def cipher_update_local(self, public_key, policy_str_new, cipher_for_local):
        """
        this part is set to update the cipher in local
        """

        # get the public_key
        pk_for_update = public_key
        # get the old access structure from the cipher_for_local
        mono_span_prog_old = cipher_for_local['MSP']
        rho = cipher_for_local['RHO']
        num_cols = cipher_for_local['NUM_COLS']
        dic_for_secret = cipher_for_local['DIC_FOR_SECRET']
        u = cipher_for_local['U']
        # initialize the update components
        uc_for_cipher = {}
        uc_for_access_structure = {}
        # generate the new access structure
        policy_new = self.util.createPolicy(policy_str_new)
        mono_span_prog_new = self.util.convert_policy_to_msp(policy_new)
        num_cols_new = self.util.len_longest_row
        # compute the interpolation between the num_cols and num_cols_new
        interpolation = num_cols_new - num_cols
        # update the list u[] by insert the new_rand at the last of u[]
        if interpolation > 0:
            for i in range(interpolation):
                new_rand = self.group.random(ZR)
                u.append(new_rand)

        i_for_row = 0  # using for adding the row number
        for key_new, value_new in mono_span_prog_new.items():
            # generate the cipher component which is type 'alter'
            if key_new in mono_span_prog_old.keys():
                if value_new != mono_span_prog_old[key_new]:
                    len_new = len(value_new)
                    sum_new = 0
                    for i in range(len_new):
                        sum_new += value_new[i] * u[i]
                    d = sum_new - dic_for_secret[key_new]
                    # component for cipher
                    uc_for_cipher[rho[key_new]] = 'alter', pk_for_update['g1_a'] ** d
                    # component for access structure
                    uc_for_access_structure[rho[key_new]] = 'alter', value_new

            # generate the cipher component which is type 'insert'
            if key_new not in mono_span_prog_old.keys():
                i_for_row += 1
                row = len(rho) + i_for_row  # update the row
                #  xor the m_for_acf and attr_row_str
                attr_row_str = ('{:032b}'.format(int(key_new))) + ('{:032b}'.format(int(row)))
                c_for_acf = cipher_for_local['C_FOR_ACF']
                value_for_xor = ''
                for i in range(len(c_for_acf)):
                    bit = int(list(c_for_acf)[i]) ^ int(list(attr_row_str)[i])
                    value_for_xor += str(bit)

                # compute the value of sum for the new attributes
                len_new = len(value_new)
                sum_new = 0
                for i in range(len_new):
                    sum_new += value_new[i] * u[i]

                # perform the encryption algorithm for the attribute which is going to be inserted
                attr_stripped = self.util.strip_index(key_new)
                r_attr = self.group.random(ZR)
                c_attr = (pk_for_update['g1_a'] ** sum_new) / (pk_for_update['h'][int(attr_stripped)] ** r_attr)
                d_attr = pk_for_update['g2'] ** r_attr

                # component for cipher
                uc_for_cipher[row] = 'insert', c_attr, d_attr
                # component for access structure
                fingerprint = hashutils.fingerprint(key_new, self.fingerprint_size)
                uc_for_access_structure[row] = 'insert', value_new, fingerprint, value_for_xor
                # update the dic_for_secret[]
                dic_for_secret[key_new] = sum

        # generate the cipher component which is type 'delete'
        for key_old, value_old in mono_span_prog_old.items():
            if key_old not in mono_span_prog_new.keys():
                fingerprint = hashutils.fingerprint(key_old, self.fingerprint_size)
                # component for cipher
                uc_for_cipher[rho[key_old]] = 'delete', None
                # component for access structure
                uc_for_access_structure[rho[key_old]] = 'delete', fingerprint

        return {'UC_FOR_CIPHER': uc_for_cipher, 'UC_FOR_ACCESS_STRUCTURE': uc_for_access_structure}



