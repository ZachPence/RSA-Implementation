from typing import Tuple
from random import randint
from math import gcd, log, floor 

class RSA():
    def __init__(self) -> None:
        pass

    def encrypt(self, message, public_key):
        # Unpack Tuple
        exponent, modulus = public_key

        return self._modExp(message, exponent, modulus)

    def decrypt(self, ciphertext, private_key):
        # Unpack Tuple
        private_exponent, prime1, prime2 = private_key

        # Pre-Requisites to use the Chinese Remainder Theorem
        X1 = self._modExp(ciphertext % prime1, private_exponent % (prime1 - 1), prime1)
        X2 = self._modExp(ciphertext % prime2, private_exponent % (prime2 - 1), prime2)

        # Per the Chinese Remainder Theorem, there is an m such that m % prime1 = x1 
        # m % prime2 = x2
        # m is our original message (named as such)

        M_1 = (prime1 * prime2) // prime1
        M_2 = (prime1 * prime2) // prime2

        M_1_INV = self._inverse_mod(M_1, prime1)
        M_2_INV = self._inverse_mod(M_2, prime2)

        plaintext = (X1*M_1*M_1_INV + X2*M_2*M_2_INV) % (prime1*prime2)
        return plaintext

    def sign(self, message, private_key):
        # Un-Pack Tuple
        private_exponent, prime1, prime2 = private_key


        # Pre-Requisites to use the Chinese Remainder Theorem
        X1 = self._modExp(message, private_exponent % (prime1 - 1), prime1)
        X2 = self._modExp(message, private_exponent % (prime2 - 1), prime2)

        # Per the Chinese Remainder Theorem, there is an s such that s % prime1 = x1 
        # s % prime2 = x2
        # s is our signature

        M_1 = (prime1 * prime2) // prime1
        M_2 = (prime1 * prime2) // prime2

        M_1_INV = self._inverse_mod(M_1, prime1)
        M_2_INV = self._inverse_mod(M_2, prime2)

        signature = (X1*M_1*M_1_INV + X2*M_2*M_2_INV) % (prime1*prime2)

        return (message, signature)

    def verify(self, signed_message, public_key):
        # Unpack Tuples 
        message, signature = signed_message
        public_modulus, public_exponent = public_key

        return message == self._modExp(signature, public_exponent, public_modulus)

    def primeTest(self, canidate: int) -> bool:
        """Use the Miller-Rabin Primality Test to see if a number is prime"""
        # For efficiency, we will see if the number is divisible 
        # By the first 100 primes
        PRIME_LIST: Tuple[int] = (2, 3, 5, 7, 11, 
                                    13, 17, 19, 23, 
                                    29, 31, 37, 41, 
                                    43, 47, 53, 59, 
                                    61, 67, 71, 73, 
                                    79, 83, 89, 97, 
                                    101, 103, 107, 109, 113, 
                                    127, 131, 137, 139, 149, 
                                    151, 157, 163, 167, 173, 
                                    179, 181, 191, 193, 197, 
                                    199, 211, 223, 227, 229, 
                                    233, 239, 241, 251, 257, 
                                    263, 269, 271, 277, 281, 
                                    283, 293, 307, 311, 313, 
                                    317, 331, 337, 347, 349, 
                                    353, 359, 367, 373, 379, 
                                    383, 389, 397, 401, 409, 
                                    419, 421, 431, 433, 439, 
                                    443, 449, 457, 461, 463, 
                                    467, 479, 487, 491, 499, 
                                    503, 509, 521, 523, 541)
        if canidate in PRIME_LIST:
            return True
        else:
            for prime in PRIME_LIST:
                if canidate % prime == 0:
                    return False 

        # Otherwise, begin the test:

        # Find u,r such that canidate - 1 = (2**u)*r
        u = 0
        while (canidate - 1) % (2 ** (u+1)) == 0:
            u += 1
        r = (canidate - 1) // 2 ** u

        SECURITY_PARAMETER = 100
        for i in range(SECURITY_PARAMETER):
            rand_num = randint(2, canidate - 2)
            iterator = self._modExp(rand_num, r, canidate)
            if iterator == 1 or iterator == canidate - 1:
                return True
            else:
                for j in range(1, u-1):
                    iterator = self._modExp(iterator, 2, canidate)
                    if iterator == 1 and not iterator != canidate - 1:
                        return False

        return True
            
    def generate_keys(self, p,q) -> Tuple[Tuple[int], int]:
        # Validate p and q are prime
        if not self.primeTest(p) or not self.primeTest(q):
            raise ValueError("One of the arguments is not a prime number.")
        
        phi_n = (p-1)*(q-1)
        
        # We will intentionally pick the value of e
        # to be in the form 2^k + 1 for faster
        # encryption
        k_max = floor(log(phi_n - 1))
        k = randint(1, k_max)

        e = (2**k) + 1
        while gcd(e, phi_n) != 1:
            k = randint(1, k_max)
            e = (2**k) + 1

        # Calculate the private key
        # Which is e^-1 mod phi_n 
        e_neg1 = self._inverse_mod(e, phi_n)

        return (p*q, e), (e_neg1, p, q) # public_key, private_key

    def _modExp(self, base, power, modulus) -> int:
        """Use the Square and Multiply Algorithm to calculate base^power modulo (modulus)"""

        exponent: bin = bin(power)[2:]

        output = base
        for bit in exponent[1:]:
            output = (output**2) % modulus
            if bit == '1':
                output = (output*base) % modulus
            
        return output

    def _inverse_mod(self, element, modulus):
        """Compute the multiplicative inverse of element mod modulus"""
        # (The code below is the relevant part of the Extended Euclidean Algorithm)
        v0, element_inverse = 0,1

        remainder_iminus1 = modulus           # Aliases 
        remainder = element     # So its value can change in the loop
        while remainder > 1: # We have verified that gcd(element, modulus) = 1. So this will work
            quotient = remainder_iminus1 // remainder
            remainder, remainder_iminus1 = remainder_iminus1 % remainder, remainder 
            # Needs to be assigned on one line. Otherwise the new value of remainder will affect the remainder variable
            # Update values of u and v
            v0, element_inverse = element_inverse, v0 - quotient * element_inverse

        return element_inverse





def main() -> None:
    r = RSA()
    
        
if __name__ == "__main__":
    main()