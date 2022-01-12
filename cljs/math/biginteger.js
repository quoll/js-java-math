/*
 * Copyright (c) 2022, Paula Gearon. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 3 only, as
 * published by the Free Software Foundation. This file is subject to
 * the "Classpath" exception as provided in the LICENSE file that
 * accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 3 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 3 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Portions Copyright (c) 1996, 2021, Oracle and/or its affiliates.  All rights reserved.
 * Portions Copyright (c) 1995  Colin Plumb.  All rights reserved.
 *
 */

/**
 * @fileoverview Defines a BigInteger class for representing immutable
 * arbitrary-precision integers.
 */

const LONG_MASK = 0xffffffff;
const MAX_MAG_LENGTH = 0x80000000 / 32;
const PRIME_SEARCH_BIT_LENGTH_LIMIT = 500000000;
const KARATSUBA_THRESHOLD = 80;
const TOOM_COOK_THRESHOLD = 240;
const KARATSUBA_SQUARE_THRESHOLD = 128;
const BURNIKEL_ZIEGLER_THRESHOLD = 80;
const BURNIKEL_ZIEGLER_OFFSET = 40;
const SCHOENHAGE_BASE_CONVERSION_THRESHOLD = 20;
const MULTIPLY_SQUARE_THRESHOLD = 20;
const MONTGOMERY_INTRINSIC_THRESHOLD = 512;
const MIN_RADIX = 2;
const MAX_RADIX = 36;
const INT_MASK = 0xFFFFFFFF;
const MAX_INT = 0x7FFFFFFF;
const MIN_INT = 0x80000000 | 0;
const TWO_32 = INT_MASK + 1;
const LOG_TWO = Math.log(2);

// forward declaration of BigInteger values
var _ZERO;
var _ONE;
var _TWO;
var _NEGATIVE_ONE;
var _TEN;

var _SMALL_PRIME_PRODUCT;

const MAX_CONSTANT = 16;
const posConst = new Array(MAX_CONSTANT + 1);
const negConst = new Array(MAX_CONSTANT + 1);

const powerCache = new Array(MAX_RADIX + 1);
const logCache = new Array(MAX_RADIX + 1);

// This is used by the String constructor of BigInteger
const bitsPerDigit = [
    0, 0,
    1024, 1624, 2048, 2378, 2648, 2875, 3072, 3247, 3402, 3543, 3672,
    3790, 3899, 4001, 4096, 4186, 4271, 4350, 4426, 4498, 4567, 4633,
    4696, 4756, 4814, 4870, 4923, 4975, 5025, 5074, 5120, 5166, 5210,
    5253, 5295];

const digitsPerInt = [
    0, 0, 30, 19, 15, 13, 11,
    11, 10, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5];

const intRadix = [
    0, 0,
    0x40000000, 0x4546b3db, 0x40000000, 0x48c27395, 0x159fd800,
    0x75db9c97, 0x40000000, 0x17179149, 0x3b9aca00, 0xcc6db61,
    0x19a10000, 0x309f1021, 0x57f6c100, 0xa2f1b6f,  0x10000000,
    0x18754571, 0x247dbc80, 0x3547667b, 0x4c4b4000, 0x6b5a6e1d,
    0x6c20a40,  0x8d2d931,  0xb640000,  0xe8d4a51,  0x1269ae40,
    0x17179149, 0x1cb91000, 0x23744899, 0x2b73a840, 0x34e63b41,
    0x40000000, 0x4cfa3cc1, 0x5c13d840, 0x6d91b519, 0x39aa400];

class NumberFormatException extends Error {}

class ArithmeticException extends Error {}

function checkFromIndexSize(fromIndex, size, length) {
    if (length < 0 || fromIndex < 0 || size < 0 || size > length - fromIndex) {
        throw new RangeError("Accessing array outside of bounds.");
    }
}

/**
 * Returns a cope of the input array stripped of any leading zero bytes.
 * Converts the byte array into an array of 32-bit integers.
 * @param {number[]} mag  The array of bytes to process.
 * @param {number} offset  The offset into the array to start processing.
 * @param {number} length  The number of bytes to process from the array.
 * @returns {number[]} An array of 32-bit integers with packed values from the initial bytes.
 */
function stripLeadingZeroBytes(mag, offset, length) {
    const indexBound = offset + length;

    // Find first nonzero byte
    for (var keep = offset; keep < indexBound && mag[keep] === 0; keep++) ;

    // Allocate new array and copy relevant part of input array
    const intLength = ((indexBound - keep) + 3) >>> 2;
    const result = new Array(intLength);
    var b = indexBound - 1;
    for (var i = intLength - 1; i >= 0; i--) {
        result[i] = mag[b--] & 0xff;
        const bytesRemaining = b - keep + 1;
        const bytesToTransfer = Math.min(3, bytesRemaining);
        for (var j = 8; j <= (bytesToTransfer << 3); j += 8) {
            result[i] |= ((mag[b--] & 0xff) << j);
        }
    }
    return result;
}

/**
 * Multiply a pair of 32-bit values, and add in a carry that is up to 16-bits
 * @param {number} a  The first 32-bit integer to multiply.
 * @param {number} b  The second 32-bit integer to multiply.
 * @param {number} carry  A 32-bit "carry" value to be added to the result.
 * @return {number[]} A pair of 32-bit values representing the high and low words of the 64-bit result.
 */
function multiplyCarryInt(a, b, carry) {
    const al = 0xFFFF & a
    const ah = a >>> 16;
    const bl = 0xFFFF & b;
    const bh = b >>> 16;

    const blal = bl * al;
    const blah = bl * ah;
    const bhal = bh * al;
    const bhah = bh * ah;

    var p0 = blal + carry;
    var p1 = blah + bhal + (p0 >>> 16);
    p0 &= 0xFFFF;
    var p32 = bhah + (p1 >>> 16);
    // p1 &= 0xFFFF;
    return [p32, p1 << 16 | p0];
}

/**
 * Converts an integer that may be in 32-bit form into an unsigned integer in the 52-bit space that Number permits
 * @param {number} n  The integer to convert
 */
function unsignedLonger(n) {
    if (n >= 0) return n;
    if (n < MIN_INT) throw new RangeError(`Value ${n} is outside of unsigned int range`);
    return (n & MAX_INT) + 0x80000000;
}

/**
 * Multiply x array times integer y in place, and add integer z
 * @param {number[]} x  An array of 32 bit integer values.
 * @param {number} y  An unsigned 32 bit value to multiply the array by.
 * @param {number} z  An unsigned 32 bit value to add to the array.
 */
function destructiveMulAdd(x, y, z) {
    const len = x.length;

    var product_low = 0;
    var carry = 0;
    for (var i = len - 1; i >= 0; i--) {
        [carry, x[i]] = multiplyCarryInt(y, x[i], carry);
    }

    // Perform the addition
    var sum = unsignedLonger(x[len - 1]) + unsignedLonger(z);
    x[len - 1] = sum & INT_MASK;
    carry = Math.floor(sum / TWO_32);  // equivalent to >>>32
    for (var i = len - 2; i >= 0; i--) {
        sum = unsignedLonger(x[i]) + carry;
        x[i] = sum & INT_MASK;
        carry = Math.floor(sum / TWO_32);
    }
}

/**
 * Returns the input array stripped of any leading zero bytes.
 * If the source is trusted then the copying may be skipped.
 * @param {number[]} value  The integer array to strip zeros from.
 * @param {boolean} trusted  Indicates if the value array can be trusted not to change.
 * @param {number[]} An integer array with no leading zeros. This may be the original array.
 */
function stripLeadingZeroInts(value, trusted = false) {
    const vlen = value.length;

    // Find first nonzero byte
    for (var keep = 0; keep < vlen && value[keep] == 0; keep++);

    return trusted && keep === 0 ? value : value.slice(keep, vlen);
}

/**
 * Throws an ArithmeticException if the BigInteger would be
 * out of the supported range.
 *
 * @throws {ArithmeticException} if this exceeds the supported range.
 */
function checkRange(mag) {
    if (mag.length > MAX_MAG_LENGTH || mag.length == MAX_MAG_LENGTH && mag[0] < 0) {
        reportOverflow();
    }
}

/**
 * Throws an ArithmeticException with a consistent error message for reporting an overflow.
 * @throws {ArithmeticException} always.
 */
function reportOverflow() {
    throw new ArithmeticException('BigInteger would overflow supported range');
}

/**
 * Creates an integer array with numBits of random bits, 8 bits per integer.
 * @param {number} numBits  The number of random bits to generate.
 * @returns {number[]} The array containing 8 bit integers of random bits.
 * TODO: add optional certainty argument for probable prime generation.
 */
function randomBits(numBits) {
    if (numBits < 0) throw new RangeError('numBits myst be non-negative');
    var numInts = Math.floor((numBits + 31) / 32);
    var randomBits = new Uint32Array(numInts);
    if (numInts > 0) {
        var crpt = (typeof self === 'undefined') ? global.crypto.webcrypto : self.crypto;
        crpt.getRandomValues(randomBits);
        var excessBits = 32 * numInts - numBits;
        randomBits[0] &= (1 << (32 - excessBits)) - 1;
    }
    return randomBits;
}

/**
 * Adds the contents of the int arrays x and y. Allocates a new int array to hold the answer
 * and returns a reference to that array.
 * @param {number[]} x The first int array to add.
 * @param {number[]} y The second int array to add.
 */
function addMagnitudes(x, y) {
    if (x.length < y.length) [x, y] = [y, x];
    var xIndex = x.length;
    var yIndex = y.length;
    const result = new Array(xIndex);
    var sum = 0;
    if (yIndex === 1) {
        sum = unsignedLonger(x[--xIndex]) + unsignedLonger(y[0]);
        result[xIndex] = sum;
    } else {
        // Add common parts of both numbers
        while (yIndex > 0) {
            sum = unsignedLonger(x[--xIndex]) + unsignedLonger(y[--yIndex]) + Math.floor(sum / TWO_32);
            result[xIndex] = sum & INT_MASK;
        }
    }
    // Copy remainder of longer number while carry propagation is required
    var carry = (sum > INT_MASK);
    while (xIndex > 0 && carry) {
        sum = unsignedLonger(x[--xIndex]) + 1;
        result[xIndex] = sum & INT_MASK;
        carry = (sum > INT_MASK);
    }
    // Copy remainder of longer number
    while (xIndex > 0) result[--xIndex] = x[xIndex];
    // Grow result if necessary
    if (carry) {
        var newResult = new Array(result.length + 1);
        for (var i = 0; i < result.length; i++) newResult[i + 1] = result[i];
        newResult[0] = 1;
        return newResult;
    }
    return result;
}

/**
 * Subtracts the contents of the int arrays x and y. Allocates a new int array to hold the answer.
 * @param {number[]} big The first int array to subtract.
 * @param {number[]} little The second int array to subtract. This must be shorted than the big array.
 */
function subtractMagnitudes(big, little) {
    if (big.length < little.length) throw new RangeError('big array must be longer than little array');
    var bigIndex = big.length;
    var littleIndex = little.length;
    const result = new Array(bigIndex);
    var difference = 0;
    if (littleIndex === 1) {
        difference = unsignedLonger(big[--bigIndex]) - unsignedLonger(little[0]);
        result[bigIndex] = difference & INT_MASK;
    } else {
        // Subtract common parts of both numbers
        while (littleIndex > 0) {
            difference = unsignedLonger(big[--bigIndex]) - unsignedLonger(little[--littleIndex]) + Math.floor(difference / TWO_32);
            result[bigIndex] = difference & INT_MASK;
        }
    }
    // Subtract remainder of longer number while borrow propagates
    var borrow = (difference > INT_MASK);
    while (bigIndex > 0 && borrow) {
        difference = (unsignedLonger(big[--bigIndex]) - 1) & INT_MASK;
        result[bigIndex] = difference;
        borrow = difference === -1;
    }
    // Copy remainder of longer number
    while (bigIndex > 0) result[--bigIndex] = big[bigIndex];
    // Get rid of leading zeros
    return stripLeadingZeroInts(result, true);
}

/**
 * Compares the contents of the int arrays x and y.
 * @param {number[]} x The first int array to compare.
 * @param {number[]} y The second int array to compare.
 */
function compareMagnitudes(x, y) {
    const xIndex = x.length;
    const yIndex = y.length;
    if (xIndex === yIndex) {
        for (var i = 0; i < xIndex; i++) {
            if (x[i] !== y[i]) return unsignedLonger(x[i]) < unsignedLonger(y[i]) ? -1 : 1;
        }
        return 0;
    }
    return xIndex < yIndex ? -1 : 1;
}

/**
 * Counts the number of bits set to 1 in the integer n.
 * @param {number} n  A 32-bit integer.
 * @returns The number of bits set to 1 in the integer n, from 0 to 32.
 */
function bitCount(n) {
    n = n - ((n >> 1) & 0x55555555);
    n = (n & 0x33333333) + ((n >> 2) & 0x33333333);
    return ((n + (n >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
}

/**
 * Returns the length of the bits required to represent the integer n in binary.
 * @param {number} n A 32-bit integer.
 * @returns The shortest number of bits required to represent the integer n in binary.
 */
function bitLengthForInt(n) {
    return 32 - (n | 0).toString(2).length;
}

/**
 * Returns the value radix^(2^exponent) from the cache.
 * If this value doesn't already exist int he cache, it is added.
 * @param {number} radix The base of the power.
 * @param {number} exponent The exponent of the power.
 * @returns radix^(2^exponent)
 */
function getRadixConversionCache(radix, exponent) {
    var cacheLine = powerCache[radix];
    if (exponent < cacheLine.length) return cacheLine[exponent];

    newCacheLine = new Array(exponent + 1);
    for (var i = 0; i < cacheLine.length; i++) newCacheLine[i] = cacheLine[i];
    for (; i < newCacheLine.length; i++) {
        cacheLine[i] = cacheLine[i - 1].pow(2);
    }
    
    if (exponent >= powerCache[radix].length) {
        powerCache[radix] = newCacheLine;
    }
    return cacheLine[exponent];
}

function smallToString(u, radix, s, digits) {
    
}

function toString(u, s, radix, digits) {
    if (u.mag.length <= SCHOENHAGE_BASE_CONVERSION_THRESHOLD) {
        return smallToString(u, radix, s, digits);
    }
    var b = u.bitLength();
    var n = Math.round(Math.log(b * LOG_TWO / logCache[radix]) / LOG_TWO - 1);
    var v = getRadixConversionCache(radix, n);
    var results = u.divideAndRemainder(v); // TODO
    var expectedDigits = 1 << n;
    // Now recursively build the two halves of each number
    return toString(results[0], s, radix, digits - expectedDigits) +
           toString(results[1], s, radix, expectedDigits);
}

class BigInteger {
    #signum;
    #mag;
    #bitCountPlusOne;
    #bitLengthPlusOne;
    #lowestSetBitPlusTwo;
    #firstNonzeroIntNumPlusTwo;
  
    // static initialization of constant values.
    // These values are all vars, but are invisible outside this file, except through static getters.
    static {
        for (var i = 1; i <= MAX_CONSTANT; i++) {
            posConst[i] = new BigInteger(1, [i]);
            negConst[i] = new BigInteger(-1, [i]);
        }
        _ZERO = new BigInteger(0, []);
        _ONE = BigInteger.valueOf(1);
        _TWO = BigInteger.valueOf(2);
        _NEGATIVE_ONE = BigInteger.valueOf(-1);
        _TEN = BigInteger.valueOf(10);
        _SMALL_PRIME_PRODUCT = new BigInteger(1, [0x8a5b, 0x6470af95])
        for (var i = MIN_RADIX; i < MAX_RADIX; i++) {
            powerCache[i] = [new BigInteger(1, [i])];
            logCache[i] = Math.log(i);
        }
    }

    /**
     * @param {number} signum  Contains a number representing the sign of the integer. May only be one of: [-1, 0 1]
     * @param {number[]} magnitude  An array of 32-bit integers containing the full value of the BigInteger.
     */
    constructor(signum, magnitude) {
        if (signum < -1 || signum > 1) {
            throw new NumberFormatException('Invalid signum value');
        }
        if (magnitude.length <= 1) {
            // declaration of constants
            if ((magnitude.length === 0 && signum !== 0) || (magnitude.length === 1 && signum === 0)) {
                throw new NumberFormatException('Invalid signum value');
            }
            this.#signum = signum;
            this.#mag = magnitude;
        } else {
            checkFromIndexSize(0, magnitude.length, magnitude);
            magnitude.forEach((item) => {
                if (item > MAX_INT || item < MIN_INT) {
                    throw NumberFormatException('Magnitude array must be 32 bit integer values');
                }
            });
            
            this.#mag = stripLeadingZeroInts(magnitude);
            if (this.#mag.length == 0) {
                this.#signum = 0;
            } else {
                if (signum === 0) throw new NumberFormatException('signum-magnitude mismatch');
                this.#signum = signum;
            }
            if (this.#mag.length >= MAX_MAG_LENGTH) checkRange(this.#mag);
        }
        this.#bitCountPlusOne = 0;
        this.#bitLengthPlusOne = 0;
        this.#lowestSetBitPlusTwo = 0;
        this.#firstNonzeroIntNumPlusTwo = 0;
    }

    /**
     * @returns {number[]} The internal magnitude array.
     */
    get mag() { return this.#mag; }

    static get ZERO() { return _ZERO; };
    static get ONE() { return _ONE; };
    static get TWO() { return _TWO; };
    static get NEGATIVE_ONE() { return _NEGATIVE_ONE; };
    static get TEN() { return _TEN; };

    static fromSlice(signum, magnitude, offset, len) {
        return new BigInteger(signum, magnitude.slice(offset, offset + len));
    }

    static fromString(value, radix = 10) {
        var cursor = 0, numDigits;
        const len = value.length;

        if (radix < MIN_RADIX || radix > MAX_RADIX) throw new RangeError("Radix out of range");
        if (len == 0) throw new NumberFormatException("Zero length BigInteger");

        // Check for at most one leading sign
        var sign = 1;
        var index1 = value.lastIndexOf('-');
        var index2 = value.lastIndexOf('+');
        if (index1 >= 0) {
            if (index1 != 0 || index2 >= 0) {
                throw new NumberFormatException("Illegal embedded sign character");
            }
            sign = -1;
            cursor = 1;
        } else if (index2 >= 0) {
            if (index2 != 0) {
                throw new NumberFormatException("Illegal embedded sign character");
            }
            cursor = 1;
        }
        if (cursor === len) throw new NumberFormatException("Zero length BigInteger");

        // Skip leading zeros and compute number of digits in magnitude
        while (cursor < len && Number.parseInt(value.charAt(cursor), radix) === 0) {
            cursor++;
        }

        if (cursor === len) {
            return new BigInteger(0, ZERO.mag);
        }

        numDigits = len - cursor;
        var signum = sign;

        // Pre-allocate array of expected size. May be too large but can
        // never be too small. Typically exact.
        var numBits = ((numDigits * bitsPerDigit[radix]) >>> 10) + 1;
        if (numBits + 31 >= 0x100000000) {
            reportOverflow();
        }
        var numWords = (numBits + 31) >>> 5;
        var magnitude = new Array(numWords);

        // Process first (potentially short) digit group
        var firstGroupLen = numDigits % digitsPerInt[radix];
        if (firstGroupLen == 0) firstGroupLen = digitsPerInt[radix];
        var group = value.substring(cursor, cursor += firstGroupLen);
        magnitude[numWords - 1] = Number.parseInt(group, radix);
        if (magnitude[numWords - 1] < 0) throw new NumberFormatException('Illegal digit');

        // Process remaining digit groups
        var superRadix = intRadix[radix];
        var groupVal = 0;
        while (cursor < len) {
            group = value.substring(cursor, cursor += digitsPerInt[radix]);
            groupVal = Number.parseInt(group, radix);
            if (groupVal < 0) throw new NumberFormatException('Illegal digit');
            destructiveMulAdd(magnitude, superRadix, groupVal);
        }
        // Required for cases where the array was overallocated.
        mag = stripLeadingZeroInts(magnitude, true);
        if (mag.length >= MAX_MAG_LENGTH) {
            checkRange();
        }
    }

    /**
     * Creates a randomly generated BigInteger.
     */
    static randomValue(numBits) {
        var magnitude = randomBits(numBits);
        magnitude = stripLeadingZeroBytes(magnitude, 0, magnitude.length);
        var signum = 1;
        if (magnitude.length === 0) signum = 0;
        if (magnitude.length >= MAX_MAG_LENGTH) checkRange();
        return new BigInteger(signum, magnitude);
    }

    static valueOf(n) {
        if (n === 0) return ZERO;
        if (n > 0 && n <= MAX_CONSTANT) {
            return posConst[val];
        } else {
            return negConst[-val];
        }
        var signum = 1;
        if (n < 0) {
            n = -n;
            signum = -1;
        }
        return new BigInteger(signum, [n]);
    }

    /**
     * Private sum operation between this and another BigInteger.
     * @param {BigInteger} val The BigInteger to add to this BigInteger.
     * @returns A new BigInteger whose value is the sum of the two numbers.
     */
    #addBigInteger(val) {
        if (val.#signum === 0) return this;
        if (this.#signum === 0) return val;
        if (this.#signum === val.#signum) {
            return new BigInteger(this.#signum, addMagnitudes(this.#mag, val.#mag));
        }
        var cmp = compareMagnitudes(this.#mag, val.#mag);
        if (cmp === 0) return ZERO;
        var resultMag = cmp > 0 ? subtractMagnitudes(this.#mag, val.#mag)
                                : subtractMagnitudes(val.#mag, this.#mag);
        return new BigInteger(cmp * this.#signum, resultMag);
    }

    /**
     * Private sum operation between this and an integer.
     * @param {number} val The number to add to this BigInteger.
     */
    #addInteger(val) {
        if (val === 0) return this;
        if (this.#signum === 0) return BigInteger.valueOf(val);
        if (this.#signum === val < 0 ? -1 : 1) {
            return new BigInteger(this.#signum, addMagnitudes(this.#mag, [this.#signum * val]));
        }
        var cmp = compareMagnitudes(this.#mag, [val]);
        if (cmp === 0) return _ZERO;
        val = Math.abs(val)
        var resultMag = cmp > 0 ? subtractMagnitudes(this.#mag, [val]) : subtractMagnitudes([val], this.#mag);
        resultMag = stripLeadingZeroInts(resultMag, true);
        return new BigInteger(cmp === this.#signum ? 1 : -1, resultMag);
    }

    /**
     * Private difference operation between this and another BigInteger.
     * @param {BigInteger} val The BigInteger to subtract from this BigInteger.
     * @returns A new BigInteger whose value is the difference of the two numbers.
     */
    #subtractBigInteger(val) {
        if (val.#signum === 0) return this;
        if (this.#signum === 0) return val.negate();
        if (this.#signum !== val.#signum) {
            return new BigInteger(this.#signum, addMagnitudes(this.#mag, val.#mag));
        }
        var cmp = compareMagnitudes(this.#mag, val.#mag);
        if (cmp === 0) return ZERO;
        var resultMag = cmp > 0 ? subtractMagnitudes(this.#mag, val.#mag)
                                : subtractMagnitudes(val.#mag, this.#mag);
        return new BigInteger(cmp === this.#signum ? 1 : -1, resultMag);
    }

    /**
     * Private difference operation between this and an integer.
     * @param {number} val The number to subtract from this BigInteger.
     */
    #subtractInteger(val) {
        if (val === 0) return this;
        if (this.#signum === 0) return BigInteger.valueOf(val).negate();
        var resultMag = subtractFromMagnitude(this.#mag, val);
        if (resultMag.length >= MAX_MAG_LENGTH) checkRange();
        return new BigInteger(this.#signum, resultMag);
    }

    /**
     * Returns a BigInteger whose value is this + val.
     * @param {Object} val  The BigInteger or integer to add to this BigInteger.
     */
    add(val) {
        if (val instanceof BigInteger) {
            return this.#addBigInteger(val);
        } else if (typeof val === 'number') {
            return this.#addInteger(val);
        } else {
            throw new TypeError('Invalid argument type');
        }
    }
    
    /**
     * Returns a BigInteger whose value is this - val.
     * @param {Object} val  The BigInteger or integer to subtract from this BigInteger.
     */
    subtract(val) {
        if (val instanceof BigInteger) {
            return this.#subtractBigInteger(val);
        } else if (typeof val === 'number') {
            return this.#subtractInteger(val);
        } else {
            throw new TypeError('Invalid argument type');
        }
    }
    
    /**
     * Returns a BigInteger whose value is -this.
     * @returns {BigInteger} -this
     */
    negate() {
        if (this.#signum === 0) return this;
        return new BigInteger(-this.#signum, this.#mag);
    }

    /**
     * Returns a BigInteger whose value is the absolute value of this.
     * @returns {BigInteger} abs(this)
     */
    abs() {
        return this.#signum < 0 ? this.negate() : this;
    }

    /**
     * Returns the number of bits in the minimal two's-complement representation of this BigInteger,
     * excluding a sign bit. For positive BigIntegers, this is equivalent to the number of bits in
     * the ordinary binary representation. For zero this method returns 0.
     * @returns number of bits in the minimal two's-complement representation of this BigInteger,
     *          excluding a sign bit.
     */
    bitLength() {
        var n = this.#bitLengthPlusOne - 1;
        if (n === -1) {
            var m = this.#mag
            var len = m.length;
            if (len === 0) { 
                n = 0;  // offset by one to initialize
            } else {
                var magBitLength = ((len - 1) << 5) + bitLengthForInt(m[0]);
                if (signum < 0) {
                    // Check if magnitude is a power of two
                    var pow2 = bitCount(m[0]) === 1;
                    for (var i = 1; i < len && pow2; i++) pow2 = m[i] === 0;
                    n = pow2 ? magBitLength - 1 : magBitLength;
                } else {
                    n = magBitLength;
                }
            }
            this.#bitLengthPlusOne = n + 1;
        }
        return n;
    }
    
    pow(n) {

    }
    
    #divideAndRemainderKnuth(val) {
        var result = [ZERO, ZERO];
    }

    divideAndRemainder(val) {
        if (val.#mag.length < BURNIKEL_ZIEGLER_THRESHOLD ||
            this.#mag.length - val.#mag.length < BURNIKEL_ZIEGLER_OFFSET) {
            return this.divideAndRemainderKnuth(val);
        } else {
            return this.divideAndRemainderBurnikelZiegler(val);
        }
    }

    toString(radix = 10) {
        if (signum === 0) return "0";
        if (radix < MIN_RADIX || radix > MAX_RADIX) radix = 10;

        var abs = this.abs();
        return toString(abs, this.#signum < 0 ? "-" : "", radix, 0);  // TODO
    }
}

exports = BigInteger;
