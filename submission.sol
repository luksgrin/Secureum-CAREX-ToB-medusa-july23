pragma solidity 0.8.19;

/// @notice Signed 18 decimal fixed point (wad) arithmetic library.
/// @author Solmate (https://github.com/transmissions11/solmate/blob/main/src/utils/SignedWadMath.sol)
/// @author Modified from Remco Bloemen (https://xn--2-umb.com/22/exp-ln/index.html)

library SignedWadMath {
    /// @dev Will not revert on overflow, only use where overflow is not possible.
    function toWadUnsafe(uint256 x) pure internal returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Multiply x by 1e18.
            r := mul(x, 1000000000000000000)
        }
    }

    /// @dev Takes an integer amount of seconds and converts it to a wad amount of days.
    /// @dev Will not revert on overflow, only use where overflow is not possible.
    /// @dev Not meant for negative second amounts, it assumes x is positive.
    function toDaysWadUnsafe(uint256 x) pure internal returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Multiply x by 1e18 and then divide it by 86400.
            r := div(mul(x, 1000000000000000000), 86400)
        }
    }

    /// @dev Takes a wad amount of days and converts it to an integer amount of seconds.
    /// @dev Will not revert on overflow, only use where overflow is not possible.
    /// @dev Not meant for negative day amounts, it assumes x is positive.
    function fromDaysWadUnsafe(int256 x) pure internal returns (uint256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Multiply x by 86400 and then divide it by 1e18.
            r := div(mul(x, 86400), 1000000000000000000)
        }
    }

    /// @dev Will not revert on overflow, only use where overflow is not possible.
    function unsafeWadMul(int256 x, int256 y) pure internal returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Multiply x by y and divide by 1e18.
            r := sdiv(mul(x, y), 1000000000000000000)
        }
    }

    /// @dev Will return 0 instead of reverting if y is zero and will
    /// not revert on overflow, only use where overflow is not possible.
    function unsafeWadDiv(int256 x, int256 y) pure internal returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Multiply x by 1e18 and divide it by y.
            r := sdiv(mul(x, 1000000000000000000), y)
        }
    }

    function wadMul(int256 x, int256 y) pure internal returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Store x * y in r for now.
            r := mul(x, y)

            // Equivalent to require(x == 0 || (x * y) / x == y)
            if iszero(or(iszero(x), eq(sdiv(r, x), y))) {
                revert(0, 0)
            }

            // Scale the result down by 1e18.
            r := sdiv(r, 1000000000000000000)
        }
    }

    function wadDiv(int256 x, int256 y) pure internal returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Store x * 1e18 in r for now.
            r := mul(x, 1000000000000000000)

            // Equivalent to require(y != 0 && ((x * 1e18) / 1e18 == x))
            if iszero(and(iszero(iszero(y)), eq(sdiv(r, 1000000000000000000), x))) {
                revert(0, 0)
            }

            // Divide r by y.
            r := sdiv(r, y)
        }
    }

    /// @dev Will not work with negative bases, only use when x is positive.
    function wadPow(int256 x, int256 y) pure internal returns (int256) {
        // Equivalent to x to the power of y because x ** y = (e ** ln(x)) ** y = e ** (ln(x) * y)
        return wadExp((wadLn(x) * y) / 1e18); // Using ln(x) means x must be greater than 0.
    }

    function wadExp(int256 x) pure internal returns (int256 r) {
        unchecked {
            // When the result is < 0.5 we return zero. This happens when
            // x <= floor(log(0.5e18) * 1e18) ~ -42e18
            if (x <= -42139678854452767551) return 0;

            // When the result is > (2**255 - 1) / 1e18 we can not represent it as an
            // int. This happens when x >= floor(log((2**255 - 1) / 1e18) * 1e18) ~ 135.
            if (x >= 135305999368893231589) revert("EXP_OVERFLOW");

            // x is now in the range (-42, 136) * 1e18. Convert to (-42, 136) * 2**96
            // for more intermediate precision and a binary basis. This base conversion
            // is a multiplication by 1e18 / 2**96 = 5**18 / 2**78.
            x = (x << 78) / 5**18;

            // Reduce range of x to (-½ ln 2, ½ ln 2) * 2**96 by factoring out powers
            // of two such that exp(x) = exp(x') * 2**k, where k is an integer.
            // Solving this gives k = round(x / log(2)) and x' = x - k * log(2).
            int256 k = ((x << 96) / 54916777467707473351141471128 + 2**95) >> 96;
            x = x - k * 54916777467707473351141471128;

            // k is in the range [-61, 195].

            // Evaluate using a (6, 7)-term rational approximation.
            // p is made monic, we'll multiply by a scale factor later.
            int256 y = x + 1346386616545796478920950773328;
            y = ((y * x) >> 96) + 57155421227552351082224309758442;
            int256 p = y + x - 94201549194550492254356042504812;
            p = ((p * y) >> 96) + 28719021644029726153956944680412240;
            p = p * x + (4385272521454847904659076985693276 << 96);

            // We leave p in 2**192 basis so we don't need to scale it back up for the division.
            int256 q = x - 2855989394907223263936484059900;
            q = ((q * x) >> 96) + 50020603652535783019961831881945;
            q = ((q * x) >> 96) - 533845033583426703283633433725380;
            q = ((q * x) >> 96) + 3604857256930695427073651918091429;
            q = ((q * x) >> 96) - 14423608567350463180887372962807573;
            q = ((q * x) >> 96) + 26449188498355588339934803723976023;

            /// @solidity memory-safe-assembly
            assembly {
                // Div in assembly because solidity adds a zero check despite the unchecked.
                // The q polynomial won't have zeros in the domain as all its roots are complex.
                // No scaling is necessary because p is already 2**96 too large.
                r := sdiv(p, q)
            }

            // r should be in the range (0.09, 0.25) * 2**96.

            // We now need to multiply r by:
            // * the scale factor s = ~6.031367120.
            // * the 2**k factor from the range reduction.
            // * the 1e18 / 2**96 factor for base conversion.
            // We do this all at once, with an intermediate result in 2**213
            // basis, so the final right shift is always by a positive amount.
            r = int256((uint256(r) * 3822833074963236453042738258902158003155416615667) >> uint256(195 - k));
        }
    }

    function wadLn(int256 x) pure internal returns (int256 r) {
        unchecked {
            require(x > 0, "UNDEFINED");

            // We want to convert x from 10**18 fixed point to 2**96 fixed point.
            // We do this by multiplying by 2**96 / 10**18. But since
            // ln(x * C) = ln(x) + ln(C), we can simply do nothing here
            // and add ln(2**96 / 10**18) at the end.

            /// @solidity memory-safe-assembly
            assembly {
                r := shl(7, lt(0xffffffffffffffffffffffffffffffff, x))
                r := or(r, shl(6, lt(0xffffffffffffffff, shr(r, x))))
                r := or(r, shl(5, lt(0xffffffff, shr(r, x))))
                r := or(r, shl(4, lt(0xffff, shr(r, x))))
                r := or(r, shl(3, lt(0xff, shr(r, x))))
                r := or(r, shl(2, lt(0xf, shr(r, x))))
                r := or(r, shl(1, lt(0x3, shr(r, x))))
                r := or(r, lt(0x1, shr(r, x)))
            }

            // Reduce range of x to (1, 2) * 2**96
            // ln(2^k * x) = k * ln(2) + ln(x)
            int256 k = r - 96;
            x <<= uint256(159 - k);
            x = int256(uint256(x) >> 159);

            // Evaluate using a (8, 8)-term rational approximation.
            // p is made monic, we will multiply by a scale factor later.
            int256 p = x + 3273285459638523848632254066296;
            p = ((p * x) >> 96) + 24828157081833163892658089445524;
            p = ((p * x) >> 96) + 43456485725739037958740375743393;
            p = ((p * x) >> 96) - 11111509109440967052023855526967;
            p = ((p * x) >> 96) - 45023709667254063763336534515857;
            p = ((p * x) >> 96) - 14706773417378608786704636184526;
            p = p * x - (795164235651350426258249787498 << 96);

            // We leave p in 2**192 basis so we don't need to scale it back up for the division.
            // q is monic by convention.
            int256 q = x + 5573035233440673466300451813936;
            q = ((q * x) >> 96) + 71694874799317883764090561454958;
            q = ((q * x) >> 96) + 283447036172924575727196451306956;
            q = ((q * x) >> 96) + 401686690394027663651624208769553;
            q = ((q * x) >> 96) + 204048457590392012362485061816622;
            q = ((q * x) >> 96) + 31853899698501571402653359427138;
            q = ((q * x) >> 96) + 909429971244387300277376558375;
            /// @solidity memory-safe-assembly
            assembly {
                // Div in assembly because solidity adds a zero check despite the unchecked.
                // The q polynomial is known not to have zeros in the domain.
                // No scaling required because p is already 2**96 too large.
                r := sdiv(p, q)
            }

            // r is in the range (0, 0.125) * 2**96

            // Finalization, we need to:
            // * multiply by the scale factor s = 5.549…
            // * add ln(2**96 / 10**18)
            // * add k * ln(2)
            // * multiply by 10**18 / 2**96 = 5**18 >> 78

            // mul s * 5e18 * 2**96, base is now 5**18 * 2**192
            r *= 1677202110996718588342820967067443963516166;
            // add ln(2) * k * 5e18 * 2**192
            r += 16597577552685614221487285958193947469193820559219878177908093499208371 * k;
            // add ln(2**96 / 10**18) * 5e18 * 2**192
            r += 600920179829731861736702779321621459595472258049074101567377883020018308;
            // base conversion: mul 2**18 / 2**192
            r >>= 174;
        }
    }

    /// @dev Will return 0 instead of reverting if y is zero.
    function unsafeDiv(int256 x, int256 y) pure internal returns (int256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Divide x by y.
            r := sdiv(x, y)
        }
    }
}

// From https://github.com/crytic/properties/blob/main/contracts/util/PropertiesHelper.sol

abstract contract PropertiesAsserts {
    event LogUint256(string, uint256);
    event LogAddress(string, address);
    event LogString(string);

    event AssertFail(string);
    event AssertEqFail(string);
    event AssertNeqFail(string);
    event AssertGteFail(string);
    event AssertGtFail(string);
    event AssertLteFail(string);
    event AssertLtFail(string);

    function assertWithMsg(bool b, string memory reason) internal {
        if (!b) {
            emit AssertFail(reason);
            assert(false);
        }
    }

    /// @notice asserts that a is equal to b. Violations are logged using reason.
    function assertEq(uint256 a, uint256 b, string memory reason) internal {
        if (a != b) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "!=",
                bStr,
                ", reason: ",
                reason
            );
            emit AssertEqFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice int256 version of assertEq
    function assertEq(int256 a, int256 b, string memory reason) internal {
        if (a != b) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "!=",
                bStr,
                ", reason: ",
                reason
            );
            emit AssertEqFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice bool version of assertEq
    function assertEq(bool a, bool b, string memory reason) internal {
        if (a != b) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "!=",
                bStr,
                ", reason: ",
                reason
            );
            emit AssertEqFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice asserts that a is not equal to b. Violations are logged using reason.
    function assertNeq(uint256 a, uint256 b, string memory reason) internal {
        if (a == b) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "==",
                bStr,
                ", reason: ",
                reason
            );
            emit AssertNeqFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice int256 version of assertNeq
    function assertNeq(int256 a, int256 b, string memory reason) internal {
        if (a == b) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "==",
                bStr,
                ", reason: ",
                reason
            );
            emit AssertNeqFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice bool version of assertNEq
    function assertNeq(bool a, bool b, string memory reason) internal {
        if (a == b) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "==",
                bStr,
                ", reason: ",
                reason
            );
            emit AssertEqFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice asserts that a is greater than or equal to b. Violations are logged using reason.
    function assertGte(uint256 a, uint256 b, string memory reason) internal {
        if (!(a >= b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "<",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertGteFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice int256 version of assertGte
    function assertGte(int256 a, int256 b, string memory reason) internal {
        if (!(a >= b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "<",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertGteFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice asserts that a is greater than b. Violations are logged using reason.
    function assertGt(uint256 a, uint256 b, string memory reason) internal {
        if (!(a > b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "<=",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertGtFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice int256 version of assertGt
    function assertGt(int256 a, int256 b, string memory reason) internal {
        if (!(a > b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                "<=",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertGtFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice asserts that a is less than or equal to b. Violations are logged using reason.
    function assertLte(uint256 a, uint256 b, string memory reason) internal {
        if (!(a <= b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                ">",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertLteFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice int256 version of assertLte
    function assertLte(int256 a, int256 b, string memory reason) internal {
        if (!(a <= b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                ">",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertLteFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice asserts that a is less than b. Violations are logged using reason.
    function assertLt(uint256 a, uint256 b, string memory reason) internal {
        if (!(a < b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                ">=",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertLtFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice int256 version of assertLt
    function assertLt(int256 a, int256 b, string memory reason) internal {
        if (!(a < b)) {
            string memory aStr = PropertiesLibString.toString(a);
            string memory bStr = PropertiesLibString.toString(b);
            bytes memory assertMsg = abi.encodePacked(
                "Invalid: ",
                aStr,
                ">=",
                bStr,
                " failed, reason: ",
                reason
            );
            emit AssertLtFail(string(assertMsg));
            assert(false);
        }
    }

    /// @notice Clamps value to be between low and high, both inclusive
    function clampBetween(
        uint256 value,
        uint256 low,
        uint256 high
    ) internal returns (uint256) {
        if (value < low || value > high) {
            uint ans = low + (value % (high - low + 1));
            string memory valueStr = PropertiesLibString.toString(value);
            string memory ansStr = PropertiesLibString.toString(ans);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                valueStr,
                " to ",
                ansStr
            );
            emit LogString(string(message));
            return ans;
        }
        return value;
    }

    /// @notice int256 version of clampBetween
    function clampBetween(
        int256 value,
        int256 low,
        int256 high
    ) internal returns (int256) {
        if (value < low || value > high) {
            int range = high - low + 1;
            int clamped = (value - low) % (range);
            if (clamped < 0) clamped += range;
            int ans = low + clamped;
            string memory valueStr = PropertiesLibString.toString(value);
            string memory ansStr = PropertiesLibString.toString(ans);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                valueStr,
                " to ",
                ansStr
            );
            emit LogString(string(message));
            return ans;
        }
        return value;
    }

    /// @notice clamps a to be less than b
    function clampLt(uint256 a, uint256 b) internal returns (uint256) {
        if (!(a < b)) {
            assertNeq(
                b,
                0,
                "clampLt cannot clamp value a to be less than zero. Check your inputs/assumptions."
            );
            uint256 value = a % b;
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        }
        return a;
    }

    /// @notice int256 version of clampLt
    function clampLt(int256 a, int256 b) internal returns (int256) {
        if (!(a < b)) {
            int256 value = b - 1;
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        }
        return a;
    }

    /// @notice clamps a to be less than or equal to b
    function clampLte(uint256 a, uint256 b) internal returns (uint256) {
        if (!(a <= b)) {
            uint256 value = a % (b + 1);
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        }
        return a;
    }

    /// @notice int256 version of clampLte
    function clampLte(int256 a, int256 b) internal returns (int256) {
        if (!(a <= b)) {
            int256 value = b;
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        }
        return a;
    }

    /// @notice clamps a to be greater than b
    function clampGt(uint256 a, uint256 b) internal returns (uint256) {
        if (!(a > b)) {
            assertNeq(
                b,
                type(uint256).max,
                "clampGt cannot clamp value a to be larger than uint256.max. Check your inputs/assumptions."
            );
            uint256 value = b + 1;
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        } else {
            return a;
        }
    }

    /// @notice int256 version of clampGt
    function clampGt(int256 a, int256 b) internal returns (int256) {
        if (!(a > b)) {
            int256 value = b + 1;
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        } else {
            return a;
        }
    }

    /// @notice clamps a to be greater than or equal to b
    function clampGte(uint256 a, uint256 b) internal returns (uint256) {
        if (!(a > b)) {
            uint256 value = b;
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        }
        return a;
    }

    /// @notice int256 version of clampGte
    function clampGte(int256 a, int256 b) internal returns (int256) {
        if (!(a > b)) {
            int256 value = b;
            string memory aStr = PropertiesLibString.toString(a);
            string memory valueStr = PropertiesLibString.toString(value);
            bytes memory message = abi.encodePacked(
                "Clamping value ",
                aStr,
                " to ",
                valueStr
            );
            emit LogString(string(message));
            return value;
        }
        return a;
    }
}

/// @notice Efficient library for creating string representations of integers.
/// @author Solmate (https://github.com/transmissions11/solmate/blob/main/src/utils/LibString.sol)
/// @author Modified from Solady (https://github.com/Vectorized/solady/blob/main/src/utils/LibString.sol)
/// @dev Name of the library is modified to prevent collisions with contract-under-test uses of LibString
library PropertiesLibString {
    function toString(int256 value) internal pure returns (string memory str) {
        uint256 absValue = value >= 0 ? uint256(value) : uint256(-value);
        str = toString(absValue);

        if (value < 0) {
            str = string(abi.encodePacked("-", str));
        }
    }

    function toString(uint256 value) internal pure returns (string memory str) {
        /// @solidity memory-safe-assembly
        assembly {
            // The maximum value of a uint256 contains 78 digits (1 byte per digit), but we allocate 160 bytes
            // to keep the free memory pointer word aligned. We'll need 1 word for the length, 1 word for the
            // trailing zeros padding, and 3 other words for a max of 78 digits. In total: 5 * 32 = 160 bytes.
            let newFreeMemoryPointer := add(mload(0x40), 160)

            // Update the free memory pointer to avoid overriding our string.
            mstore(0x40, newFreeMemoryPointer)

            // Assign str to the end of the zone of newly allocated memory.
            str := sub(newFreeMemoryPointer, 32)

            // Clean the last word of memory it may not be overwritten.
            mstore(str, 0)

            // Cache the end of the memory to calculate the length later.
            let end := str

            // We write the string from rightmost digit to leftmost digit.
            // The following is essentially a do-while loop that also handles the zero case.
            // prettier-ignore
            for { let temp := value } 1 {} {
                // Move the pointer 1 byte to the left.
                str := sub(str, 1)

                // Write the character to the pointer.
                // The ASCII index of the '0' character is 48.
                mstore8(str, add(48, mod(temp, 10)))

                // Keep dividing temp until zero.
                temp := div(temp, 10)

                 // prettier-ignore
                if iszero(temp) { break }
            }

            // Compute and cache the final total length of the string.
            let length := sub(end, str)

            // Move the pointer 32 bytes leftwards to make room for the length.
            str := sub(str, 32)

            // Store the string's length at the start of memory allocated for our string.
            mstore(str, length)
        }
    }

    function toString(address value) internal pure returns (string memory str) {
        bytes memory s = new bytes(40);
        for (uint i = 0; i < 20; i++) {
            bytes1 b = bytes1(
                uint8(uint(uint160(value)) / (2 ** (8 * (19 - i))))
            );
            bytes1 hi = bytes1(uint8(b) / 16);
            bytes1 lo = bytes1(uint8(b) - 16 * uint8(hi));
            s[2 * i] = char(hi);
            s[2 * i + 1] = char(lo);
        }
        return string(s);
    }

    function toString(bool b) internal pure returns (string memory str) {
        if (b) {
            return "true";
        }

        return "false";
    }

    function char(bytes1 b) internal pure returns (bytes1 c) {
        if (uint8(b) < 10) return bytes1(uint8(b) + 0x30);
        else return bytes1(uint8(b) + 0x57);
    }
}

interface IVM {
    function addr(uint256) external returns (address);
    function ffi(string[] calldata) external returns (bytes memory);
    function parseBytes(string calldata) external returns (bytes memory);
    function parseBytes32(string calldata) external returns (bytes32);
    function parseAddress(string calldata) external returns (address);
    function parseUint(string calldata) external returns (uint256);
    function parseInt(string calldata) external returns (int256);
    function parseBool(string calldata) external returns (bool);
    function sign(uint256, bytes32) external returns (uint8, bytes32, bytes32);
    function toString(address) external returns (string memory);
    function toString(bool) external returns (string memory);
    function toString(uint256) external returns (string memory);
    function toString(int256) external returns (string memory);
    function toString(bytes32) external returns (string memory);
    function toString(bytes memory) external returns (string memory);
    function warp(uint64) external;
    function load(address, bytes32) external returns (bytes32);
    function store(address, bytes32, bytes32) external;
    function roll(uint256) external;
    function prank(address) external;
    function prankHere(address) external;
    function getNonce(address) external returns (uint64);
    function setNonce(address, uint64) external;
    function fee(uint256) external;
    function etch(address, bytes calldata) external;
    function difficulty(uint256) external;
    function deal(address, uint256) external;
    function coinbase(address) external;
    function chainId(uint256) external;
}

// Run with medusa fuzz --target contracts/SignedWadMathTest.sol --deployment-order SignedWadMathTest

contract SignedWadMathTest is PropertiesAsserts{
    IVM vm = IVM(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    event LogInt(string, int256);

    // The following is an example of invariant
    // It test that if x < 10**18
    // Then x <= uint(toWadUnsafe(x))
    function testtoWadUnsafe(uint256 x) public{
        x = clampLte(x, 10**18);

        int256 y = SignedWadMath.toWadUnsafe(x);

        // Ensure that x <= uint(y)
        assertLte(x, uint(y), "X should be less or equal to Y");
    }

    function testtoAndFromDaysWadUnsafeSoft(uint256 x) public {

        x = clampLte(x, 1e57); // 1.157920892373162e58 is the maximum value that can be multiplied by 10**18 without overflowing, so we clamp to 10**57 to be safe

        uint256 y = SignedWadMath.fromDaysWadUnsafe( // Cast from daysWad
            SignedWadMath.toDaysWadUnsafe(x) // Cast to daysWad
        );

        // Ensure that y <= x, because of rounding errors
        assertLte(y, x, "Y should be less or equal to X");
    }

    function testtoAndFromDaysWadIdentityForward(uint256 x) public {
        x = clampLte(x, 1e57); // 1.157920892373162e58 is the maximum value that can be multiplied by 10**18 without overflowing, so we clamp to 10**57 to be safe

        uint256 y = SignedWadMath.fromDaysWadUnsafe( // Cast from daysWad
            SignedWadMath.toDaysWadUnsafe(x) // Cast to daysWad
        );

        /*
         * So... What these functions basically do, is...
         * [imagine we don't have integer division]
         * -> toDaysWadUnsafe: floor(x*1e18/86400)
         * -> fromDaysWadUnsafe: floor(x*86400/1e18)
         * 
         * They're inverses of each other, besides the fact that there is rounding down due to integer division.
         *
         * Nonetheless, given that they're inverses, and due to the fact that we're rounding down, and numerator is substantially bigger than denominator, we know that the error is at most 1.
         *
         * But there's not always an error. I have thought about a formal proof to identify when there's going to be an error... Let's go!
         *
         * The simple intuition is that there's going to be an error when the number of seconds is not a multiple of 86400.
         * However, this is actually a superset. I.e. there are numbers that are NOT multiples of 86400 that don't have an error.
         * We can compute that by looking first at the operation toDaysWadUnsafe; i.e. floor(x*1e18/86400)
         * There are going to be rounding errors when x*1e18/86400 does not have a remainder of 0.
         * If we decompose all the factors of 86400, we get 2^7 * 3^3 * 5^2.
         * Cool enough, if we decompose all the factors of 1e18 we get 2^18 * 3^18 * 5^18.
         * Here we can see that 5^2 * 2^7 will always get "absorbed" by 5^18 * 2^18, so we can ignore them.
         * Therefore, we only need to look at 3^3 (27). This one must be cleared by x, otherwise there will be rounding errors. So, we can say that: as long as x is a multiple of 27, there will be no rounding errors. Cool! Plus, if there are rounding errors, as mentioned earlier, they will be at most 1.
         */
        if (x % 27 == 0) {
            assertEq(
                y,
                x,
                "Y should be equal to X when X is multiple of 27. i.e. rounding error is 0"
            );
        } else {
            assertEq(
                y + 1,
                x,
                "Y + 1 should be equal to X when X is NOT multiple of 27. i.e. rounding error is 1"
            );
        }        
    }

    function testtoAndFromDaysWadIdentityReverse(int256 x) public {
        x = clampLte(x, 1e72); // Similar reasoning to the one employed at `testtoAndFromDaysWadUnsafeHardForward`
        x = clampGte(x, 1e18); // I assume no negative days haha
    
        int256 y = SignedWadMath.toDaysWadUnsafe( // Cast to daysWad
            SignedWadMath.fromDaysWadUnsafe(x) // Cast from daysWad
        );

        /*
         * Just the reverse case of `testtoAndFromDaysWadUnsafeHardForward`
         * Similar reasoning employed here.
         * I know, it looks a lot less elegant than the prior case
         */
        if (x % 312500000000000 == 0) {
            assertEq(
                y,
                x,
                "Y should be equal to X when X is multiple of 312500000000000. i.e. rounding error is 0"
            );
        } else {
            assertEq(
                y/10**16,
                x/10**16,
                "Y should be equal to X, except the last 16 digits, when X is NOT multiple of 312500000000000"
            );
        }        
    }

    function testMonotonicityOfLn(int256 x) public {
        x = clampGte(x, 1e18);

        int256 y = SignedWadMath.wadLn(x);

        assertGte(x, y, "X should be greater or equal to Y");
    }

    function testMonotonicityOfExp(int256 x) public {
        x = clampGte(x, 1e18);

        int256 y = SignedWadMath.wadExp(x);

        assertGte(y, x, "Y should be greater or equal to X");
    }

    function testExpLnIdentityForward(int256 x) public {
        x = clampGte(x, 1e18);

        int256 y = SignedWadMath.wadExp(SignedWadMath.wadLn(x));

        assertEq(
            y/10**64,
            x/10**64,
            "X should be equal to Y except the last 64 digits lol?"
        );
    }

    function testExpLnIdentityReverse(int256 x) public {
        x = clampGte(x, 1e18);

        int256 y = SignedWadMath.wadLn(SignedWadMath.wadExp(x));

        if (x < 1e21) {
            emit LogInt("x", x);
            emit LogInt("y", y);
            assertLte(
                x - y,
                1,
                "If X is less than 1e21, the error is at most 1"
            );
        } else {
            assertEq(
                y,
                x,
                "If X is bigger than 1e21, Y should be equal to X, i.e. no error"
            );
        }

    }

}

/// @notice Arithmetic library with operations for fixed-point numbers.
/// @author Solmate (https://github.com/transmissions11/solmate/blob/main/src/utils/FixedPointMathLib.sol)
/// @author Inspired by USM (https://github.com/usmfum/USM/blob/master/contracts/WadMath.sol)
library FixedPointMathLib {
    /*//////////////////////////////////////////////////////////////
                    SIMPLIFIED FIXED POINT OPERATIONS
    //////////////////////////////////////////////////////////////*/

    uint256 internal constant MAX_UINT256 = 2**256 - 1;

    uint256 internal constant WAD = 1e18; // The scalar of ETH and most ERC20s.

    function mulWadDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, y, WAD); // Equivalent to (x * y) / WAD rounded down.
    }

    function mulWadUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivUp(x, y, WAD); // Equivalent to (x * y) / WAD rounded up.
    }

    function divWadDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, WAD, y); // Equivalent to (x * WAD) / y rounded down.
    }

    function divWadUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivUp(x, WAD, y); // Equivalent to (x * WAD) / y rounded up.
    }

    /*//////////////////////////////////////////////////////////////
                    LOW LEVEL FIXED POINT OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function mulDivDown(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Equivalent to require(denominator != 0 && (y == 0 || x <= type(uint256).max / y))
            if iszero(mul(denominator, iszero(mul(y, gt(x, div(MAX_UINT256, y)))))) {
                revert(0, 0)
            }

            // Divide x * y by the denominator.
            z := div(mul(x, y), denominator)
        }
    }

    function mulDivUp(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Equivalent to require(denominator != 0 && (y == 0 || x <= type(uint256).max / y))
            if iszero(mul(denominator, iszero(mul(y, gt(x, div(MAX_UINT256, y)))))) {
                revert(0, 0)
            }

            // If x * y modulo the denominator is strictly greater than 0,
            // 1 is added to round up the division of x * y by the denominator.
            z := add(gt(mod(mul(x, y), denominator), 0), div(mul(x, y), denominator))
        }
    }

    function rpow(
        uint256 x,
        uint256 n,
        uint256 scalar
    ) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            switch x
            case 0 {
                switch n
                case 0 {
                    // 0 ** 0 = 1
                    z := scalar
                }
                default {
                    // 0 ** n = 0
                    z := 0
                }
            }
            default {
                switch mod(n, 2)
                case 0 {
                    // If n is even, store scalar in z for now.
                    z := scalar
                }
                default {
                    // If n is odd, store x in z for now.
                    z := x
                }

                // Shifting right by 1 is like dividing by 2.
                let half := shr(1, scalar)

                for {
                    // Shift n right by 1 before looping to halve it.
                    n := shr(1, n)
                } n {
                    // Shift n right by 1 each iteration to halve it.
                    n := shr(1, n)
                } {
                    // Revert immediately if x ** 2 would overflow.
                    // Equivalent to iszero(eq(div(xx, x), x)) here.
                    if shr(128, x) {
                        revert(0, 0)
                    }

                    // Store x squared.
                    let xx := mul(x, x)

                    // Round to the nearest number.
                    let xxRound := add(xx, half)

                    // Revert if xx + half overflowed.
                    if lt(xxRound, xx) {
                        revert(0, 0)
                    }

                    // Set x to scaled xxRound.
                    x := div(xxRound, scalar)

                    // If n is even:
                    if mod(n, 2) {
                        // Compute z * x.
                        let zx := mul(z, x)

                        // If z * x overflowed:
                        if iszero(eq(div(zx, x), z)) {
                            // Revert if x is non-zero.
                            if iszero(iszero(x)) {
                                revert(0, 0)
                            }
                        }

                        // Round to the nearest number.
                        let zxRound := add(zx, half)

                        // Revert if zx + half overflowed.
                        if lt(zxRound, zx) {
                            revert(0, 0)
                        }

                        // Return properly scaled zxRound.
                        z := div(zxRound, scalar)
                    }
                }
            }
        }
    }

    /*//////////////////////////////////////////////////////////////
                        GENERAL NUMBER UTILITIES
    //////////////////////////////////////////////////////////////*/

    function sqrt(uint256 x) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            let y := x // We start y at x, which will help us make our initial estimate.

            z := 181 // The "correct" value is 1, but this saves a multiplication later.

            // This segment is to get a reasonable initial estimate for the Babylonian method. With a bad
            // start, the correct # of bits increases ~linearly each iteration instead of ~quadratically.

            // We check y >= 2^(k + 8) but shift right by k bits
            // each branch to ensure that if x >= 256, then y >= 256.
            if iszero(lt(y, 0x10000000000000000000000000000000000)) {
                y := shr(128, y)
                z := shl(64, z)
            }
            if iszero(lt(y, 0x1000000000000000000)) {
                y := shr(64, y)
                z := shl(32, z)
            }
            if iszero(lt(y, 0x10000000000)) {
                y := shr(32, y)
                z := shl(16, z)
            }
            if iszero(lt(y, 0x1000000)) {
                y := shr(16, y)
                z := shl(8, z)
            }

            // Goal was to get z*z*y within a small factor of x. More iterations could
            // get y in a tighter range. Currently, we will have y in [256, 256*2^16).
            // We ensured y >= 256 so that the relative difference between y and y+1 is small.
            // That's not possible if x < 256 but we can just verify those cases exhaustively.

            // Now, z*z*y <= x < z*z*(y+1), and y <= 2^(16+8), and either y >= 256, or x < 256.
            // Correctness can be checked exhaustively for x < 256, so we assume y >= 256.
            // Then z*sqrt(y) is within sqrt(257)/sqrt(256) of sqrt(x), or about 20bps.

            // For s in the range [1/256, 256], the estimate f(s) = (181/1024) * (s+1) is in the range
            // (1/2.84 * sqrt(s), 2.84 * sqrt(s)), with largest error when s = 1 and when s = 256 or 1/256.

            // Since y is in [256, 256*2^16), let a = y/65536, so that a is in [1/256, 256). Then we can estimate
            // sqrt(y) using sqrt(65536) * 181/1024 * (a + 1) = 181/4 * (y + 65536)/65536 = 181 * (y + 65536)/2^18.

            // There is no overflow risk here since y < 2^136 after the first branch above.
            z := shr(18, mul(z, add(y, 65536))) // A mul() is saved from starting z at 181.

            // Given the worst case multiplicative error of 2.84 above, 7 iterations should be enough.
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))

            // If x+1 is a perfect square, the Babylonian method cycles between
            // floor(sqrt(x)) and ceil(sqrt(x)). This statement ensures we return floor.
            // See: https://en.wikipedia.org/wiki/Integer_square_root#Using_only_integer_division
            // Since the ceil is rare, we save gas on the assignment and repeat division in the rare case.
            // If you don't care whether the floor or ceil square root is returned, you can remove this statement.
            z := sub(z, lt(div(x, z), z))
        }
    }

    function unsafeMod(uint256 x, uint256 y) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Mod x by y. Note this will return
            // 0 instead of reverting if y is zero.
            z := mod(x, y)
        }
    }

    function unsafeDiv(uint256 x, uint256 y) internal pure returns (uint256 r) {
        /// @solidity memory-safe-assembly
        assembly {
            // Divide x by y. Note this will return
            // 0 instead of reverting if y is zero.
            r := div(x, y)
        }
    }

    function unsafeDivUp(uint256 x, uint256 y) internal pure returns (uint256 z) {
        /// @solidity memory-safe-assembly
        assembly {
            // Add 1 to x * y if x % y > 0. Note this will
            // return 0 instead of reverting if y is zero.
            z := add(gt(mod(x, y), 0), div(x, y))
        }
    }
}

// Run with medusa fuzz --target contracts/FixedPointMathLibTest.sol --deployment-order FixedPointMathLibTest

contract FixedPointMathLibTest is PropertiesAsserts{
    IVM vm = IVM(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    event LogUint(string, uint256);

    // The following is an example of invariant
    // It test that if z = x / y, then z <= x
    // For any x and y greater than 1 unit
    /*function testmulDivDown(uint256 x, uint256 y) public{

        // We work with a decimals of 18
        uint decimals = 10**18; 

        // Ensure x and y are geater than 1
        x = clampGte(x, decimals);
        y = clampGte(y, decimals);

        // compute z = x / y
        uint z = FixedPointMathLib.mulDivDown(x, y, decimals);

        // Ensure that z <= x
        assertLte(z, x, "Z should be less or equal to X");
    }*/

    function testSqrtMulIdentityForward(uint256 x) public {
        // Ensure x is greater than 1 unit
        x = clampGte(x, 10**18);
        x = clampLte(x, 10**38);

        // Compute y = sqrt(x*X)
        uint256 y = FixedPointMathLib.sqrt(
            x*x/10**18
        );

        assertLte(y, x, "Y should be less or equal to X due to rounding errors");
    }

    function testSqrtMulIdentityReverse(uint256 x) public {
        // Ensure x is greater than 1 unit
        x = clampGte(x, 10**18);
        x = clampLte(x, 10**38);

        uint256 y = FixedPointMathLib.sqrt(x);
        uint256 z = y*y/10**18;

        assertLte(z, x, "Z should be less or equal to X due to rounding errors");
    }

    function testSqrtPowIdentityForward(uint256 x) public {
        // Ensure x is greater than 1 unit
        x = clampGte(x, 10**18);
        x = clampLte(x, 10**38);

        uint256 y = FixedPointMathLib.sqrt(
            FixedPointMathLib.rpow(x, 2, 10**18)
        );

        assertLte(y, x, "Y should be less or equal to X due to rounding errors");
    }

    function testSqrtPowIdentityReverse(uint256 x) public {
        // Ensure x is greater than 1 unit
        x = clampGte(x, 10**18);
        x = clampLte(x, 10**38);

        uint256 y = FixedPointMathLib.rpow(
            FixedPointMathLib.sqrt(x),
            2,
            10**18
        );

        assertLte(y, x, "Y should be less or equal to X due to rounding errors");
    }

    function testPower(uint256 x, uint256 n) public {
        n = clampLte(n, 5);
        n = clampGt(n, 0);
        x = clampGte(x, 10**18);

        uint256 y = x;

        for (uint256 i; i < n; ++i) {
            y = x*y/10**18;
        }

        uint256 z = FixedPointMathLib.rpow(x, n, 10**18);

        assertLte(z, y, "Z should be less or equal to Y");
    }

}

// SECUREUM
// The following file contains ERC20/WETH/SafeTransferLib from solmate
// permit-like functions were removed (EIP-2612)

/// @notice Modern and gas efficient ERC20 
/// @author Solmate (https://github.com/transmissions11/solmate/blob/main/src/tokens/ERC20.sol)
/// @author Modified from Uniswap (https://github.com/Uniswap/uniswap-v2-core/blob/master/contracts/UniswapV2ERC20.sol)
/// @author [Secureum] EIP-2612 implementation was removed
/// @dev Do not manually set balances without updating totalSupply, as the sum of all user balances must not exceed it.
abstract contract ERC20 {
    /*//////////////////////////////////////////////////////////////
                                 EVENTS
    //////////////////////////////////////////////////////////////*/

    event Transfer(address indexed from, address indexed to, uint256 amount);

    event Approval(address indexed owner, address indexed spender, uint256 amount);

    /*//////////////////////////////////////////////////////////////
                            METADATA STORAGE
    //////////////////////////////////////////////////////////////*/

    string public name;

    string public symbol;

    uint8 public immutable decimals;

    /*//////////////////////////////////////////////////////////////
                              ERC20 STORAGE
    //////////////////////////////////////////////////////////////*/

    uint256 public totalSupply;

    mapping(address => uint256) public balanceOf;

    mapping(address => mapping(address => uint256)) public allowance;

    /*//////////////////////////////////////////////////////////////
                               CONSTRUCTOR
    //////////////////////////////////////////////////////////////*/

    constructor(
        string memory _name,
        string memory _symbol,
        uint8 _decimals
    ) {
        name = _name;
        symbol = _symbol;
        decimals = _decimals;
    }

    /*//////////////////////////////////////////////////////////////
                               ERC20 LOGIC
    //////////////////////////////////////////////////////////////*/

    function approve(address spender, uint256 amount) public virtual returns (bool) {
        allowance[msg.sender][spender] = amount;

        emit Approval(msg.sender, spender, amount);

        return true;
    }

    function transfer(address to, uint256 amount) public virtual returns (bool) {
        balanceOf[msg.sender] -= amount;

        // Cannot overflow because the sum of all user
        // balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[to] += amount;
        }

        emit Transfer(msg.sender, to, amount);

        return true;
    }

    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual returns (bool) {
        uint256 allowed = allowance[from][msg.sender]; // Saves gas for limited approvals.

        if (allowed != type(uint256).max) allowance[from][msg.sender] = allowed - amount;

        balanceOf[from] -= amount;

        // Cannot overflow because the sum of all user
        // balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[to] += amount;
        }

        emit Transfer(from, to, amount);

        return true;
    }

    /*//////////////////////////////////////////////////////////////
                        INTERNAL MINT/BURN LOGIC
    //////////////////////////////////////////////////////////////*/

    function _mint(address to, uint256 amount) internal virtual {
        totalSupply += amount;

        // Cannot overflow because the sum of all user
        // balances can't exceed the max uint256 value.
        unchecked {
            balanceOf[to] += amount;
        }

        emit Transfer(address(0), to, amount);
    }

    function _burn(address from, uint256 amount) internal virtual {
        balanceOf[from] -= amount;

        // Cannot underflow because a user's balance
        // will never be larger than the total supply.
        unchecked {
            totalSupply -= amount;
        }

        emit Transfer(from, address(0), amount);
    }
}

// ERC20 token with a burn function
contract ERC20Burn is ERC20("MyToken", "MT", 18) {

    constructor(){
        _mint(msg.sender, 10**18);
    }

    function burn(uint amount) public{
        _burn(msg.sender, amount);
    }

}

// Run with medusa fuzz --target contracts/ERC20Test.sol --deployment-order MyToken

contract MyToken is ERC20Burn {
    IVM vm = IVM(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    // Test that the total supply is always below or equal to 10**18
    function fuzz_Supply() public returns(bool){
        return totalSupply <= 10**18;
    }
}

// Example using an external testing
// See https://secure-contracts.com/program-analysis/echidna/basic/common-testing-approaches.html#external-testing
// Run with medusa fuzz --target contracts/ERC20TestAdvanced.sol --deployment-order ExternalTestingToken

// User is used a proxy account to simulate user specific interaction
contract User{
    constructor() {}
}

contract ExternalTestingToken is PropertiesAsserts{

    ERC20Burn token;

    User alice;

    IVM vm = IVM(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

    constructor() {
        // Deploy the token
        // All the token belong to the contract
        token = new ERC20Burn();

        assert(token.balanceOf(address(this)) == 10**18);

        alice = new User();

        // Transfer all the token to alice
        token.transfer(address(alice), 10**18);
        
        // Approve all the token from Alice to ExternalTestingToken
        vm.prank(address(alice));
        token.approve(address(this), 10**18);
    }

    // The following test a transfer from
    // Medusa will transfer an arbitrary amount using transferFrom
    // The invariant ensure that the balance was updated by the amount transfered
    function testTransferFrom(uint amount) public{
        
        // Ensure amount is less or equal to alice's balanc
        amount = clampLte(amount, token.balanceOf(address(alice)));
        // Ensure amount is less or equal to alice's approval to this contract
        amount = clampLte(amount, token.allowance(address(alice), address(this)));

        uint balanceBefore = token.balanceOf(address(alice));

        token.transferFrom(address(alice), address(this), amount);

        uint balanceAfter = token.balanceOf(address(alice));

        assertEq(balanceAfter - balanceBefore, amount, "The amount transfered must be equal to the expected amount");

    }

    // Test that the balance of any account is always below or equal to 10**18
    function balanceCapTest(address bob) public {
        assertLte(token.balanceOf(bob), 10**18, "The balance of any account must be below or equal to 10**18");
    }

    // Test that after a burn, the balance of the account has decreased by the amount burned
    function burnTest(uint256 amount) public {

        amount = clampLte(amount, token.balanceOf(address(alice)));

        uint256 balanceBefore = token.balanceOf(address(alice));

        vm.prank(address(alice));
        token.burn(amount);

        uint256 balanceAfter = token.balanceOf(address(alice));

        assertEq(balanceBefore - balanceAfter, amount, "The amount burned must be equal to the expected amount");
    }

}

