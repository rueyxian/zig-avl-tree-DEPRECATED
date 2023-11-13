# zig-avl-tree
#### An array-based AVL tree.

This library provides an AVL tree built upon the `ArrayList` from the standard library. It is cache-friendly and incurs far less allocation and deallocation overhead compared to linked-list-based structures.

## Example

```zig
const allocator: Allocator = testing.allocator;

var tree = try AvlTree(u32, []const u8, asc(u32)).init(allocator);
try tree.put_no_clobber(6, "six");
try tree.put_no_clobber(12, "twelve");
try tree.put_no_clobber(7, "seven");
try tree.put_no_clobber(8, "eight");
try tree.put_no_clobber(33, "thirty-three");
try tree.put_no_clobber(42, "fourty-two");
try tree.put_no_clobber(99, "ninety-nine");
try tree.put_no_clobber(21, "twenty-one");
try tree.put_no_clobber(4, "four");
try tree.put_no_clobber(5, "five");
_ = tree.remove(6);
_ = tree.remove(33);
_ = tree.remove(99);
try tree.put_no_clobber(1, "one");
try tree.put_no_clobber(2, "two");
_ = tree.remove(12);
_ = tree.remove(8);
_ = tree.remove(1);

const slice = try tree.to_owned_slice();
defer allocator.free(slice);

const expect = [_][]const u8{ "two", "four", "five", "seven", "twenty-one", "fourty-two" };
for (slice, 0..) |kv, i| {
	try testing.expectEqualSlices(u8, kv.value, expect[i]);
}

```