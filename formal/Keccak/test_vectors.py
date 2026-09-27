import hashlib
import random
import unittest
from Crypto.Hash import keccak
from vector_generator import RATE, RC, VECTORS, emit, pad, trace, step, HERE

class KeccakVectors(unittest.TestCase):
    def test_known_legacy_hashes(self):
        self.assertEqual(trace(b'')[1].hex(), 'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')
        self.assertEqual(trace(b'abc')[1].hex(), '4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45')

    def test_padding_boundaries(self):
        for n in (0,1,134,135,136,137,270,271,272,4096):
            message = bytes(n)
            result=pad(message)
            self.assertEqual(len(result), RATE*(n//RATE+1))
            self.assertEqual(result[:n],message)
            if n%RATE==135:
                self.assertEqual(result[n:],b'\x81')
            else:
                self.assertEqual(result[n],1)
                self.assertEqual(result[-1],128)
                self.assertEqual(result[n+1:-1],bytes(len(result)-n-2))

    def test_independent_native_oracle(self):
        rng=random.Random(1600)
        for n in (0,1,7,8,31,32,52,135,136,137,272,320,1024):
            message=bytes(rng.randrange(256) for _ in range(n))
            self.assertEqual(trace(message)[1],keccak.new(digest_bits=256,data=message).digest())

    def test_no_sha3_substitution(self):
        for _, message, _ in VECTORS:
            self.assertNotEqual(trace(message)[1], hashlib.sha3_256(message).digest())

    def test_digest_word_order(self):
        message=(1).to_bytes(20,'big')+bytes(32)
        result=trace(message)[1]
        self.assertEqual(int.from_bytes(result,'big'),int(result.hex(),16))
        self.assertNotEqual(int.from_bytes(result,'little'),int(result.hex(),16))
        self.assertGreaterEqual(int(result.hex(),16),2**64)

    def test_saved_round_checkpoints(self):
        for _,message,_ in VECTORS:
            blocks,_ = trace(message)
            for states in blocks:
                for r in range(24):
                    self.assertEqual(step(states[r],RC[r]),states[r+1])

    def test_generated_lean_exact(self):
        for name,message,expression in VECTORS:
            self.assertEqual((HERE/('Vector_'+name+'.lean')).read_text(),emit(name,message,expression))

    def test_lfsr_constants(self):
        self.assertEqual(len(RC),24)
        self.assertEqual(RC[0],1)
        self.assertEqual(RC[-1],0x8000000080008008)
        self.assertEqual(len(set(RC)),22)

if __name__=='__main__': unittest.main()
