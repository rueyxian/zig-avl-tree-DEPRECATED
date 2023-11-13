const std = @import("std");
const print = std.debug.print;
const testing = std.testing;
const assert = std.debug.assert;
const math = std.math;
const mem = std.mem;
const meta = std.meta;
const Allocator = std.mem.Allocator;
const ArrayListUnmanaged = std.ArrayListUnmanaged;

pub fn asc(comptime K: type) (fn (K, K) math.Order) {
    return struct {
        fn f(a: K, b: K) math.Order {
            return math.order(a, b);
        }
    }.f;
}

pub fn desc(comptime K: type) (fn (K, K) math.Order) {
    return struct {
        fn f(a: K, b: K) math.Order {
            return math.order(a, b).invert();
        }
    }.f;
}

const Lateral = enum {
    left,
    right,
    fn flip(self: Lateral) Lateral {
        return switch (self) {
            .left => .right,
            .right => .left,
        };
    }
};

pub fn AvlTree(comptime K: type, comptime V: type, comptime order_fn: fn (K, K) math.Order) type {
    return struct {
        allocator: Allocator,
        unmanaged: Unmanaged,

        const Self = @This();
        const Unmanaged = AvlTreeUnmanaged(K, V, order_fn);
        const Size = Unmanaged.Size;
        const Index = Unmanaged.Index;
        const Node = Unmanaged.Node;

        const KV = Unmanaged.KV;
        const GetOrPutResult = Unmanaged.GetOrPutResult;

        pub fn init(allocator: Allocator) !Self {
            return Self{
                .allocator = allocator,
                .unmanaged = Unmanaged{},
            };
        }

        pub fn init_capacity(allocator: Allocator, num: usize) !Self {
            return Unmanaged.init_capacity(allocator, num);
        }

        pub fn deinit(self: *Self) void {
            self.unmanaged.deinit(self.allocator);
        }

        pub fn count(self: *Self) Size {
            return self.unmanaged.count();
        }

        pub fn contains(self: *Self) ?V {
            return self.unmanaged.contains();
        }

        pub fn get_ptr(self: *Self, key: K) ?*V {
            return self.unmanaged.get_ptr(key);
        }

        pub fn get(self: *Self, key: K) ?V {
            return self.unmanaged.get(key);
        }

        pub fn get_or_put(self: *Self, key: K) !GetOrPutResult {
            return self.unmanaged.get_or_put(self.allocator, key);
        }

        pub fn put_no_clobber(self: *Self, key: K, value: V) !void {
            return self.unmanaged.put_no_clobber(self.allocator, key, value);
        }

        pub fn fetch_put(self: *Self, key: K, value: V) !?V {
            return self.unmanaged.fetch_put(self.allocator, key, value);
        }

        pub fn put(self: *Self, key: K, value: V) !void {
            return self.unmanaged.put(self.allocator, key, value);
        }

        pub fn fetch_remove(self: *Self, key: K) ?V {
            return self.unmanaged.fetch_remove(key);
        }

        pub fn remove(self: *Self, key: K) bool {
            return self.unmanaged.remove(key);
        }

        pub fn clone(self: *const Self) !Self {
            const unmanaged = try self.unmanaged.clone(self.allocator);
            return Self{
                .unmanaged = unmanaged,
                .allocator = self.allocator,
            };
        }

        pub fn to_owned_slice(self: *Self) ![]KV {
            return self.unmanaged.to_owned_slice(self.allocator);
        }

        fn walk(self: *Self) void {
            self.unmanaged.walk();
        }
    };
}

pub fn AvlTreeUnmanaged(comptime K: type, comptime V: type, comptime order_fn: fn (K, K) math.Order) type {
    return struct {
        arena: Arena = Arena{},
        root: ?Index = null,
        size: Size = 0,

        const Self = @This();

        const Size = u32;
        const Index = Size;

        fn update_height(index: Index, arena: *Arena) void {
            var n = arena.get_node(index);
            const lh = if (n.left) |i| arena.get_node(i).height else 0;
            const rh = if (n.right) |i| arena.get_node(i).height else 0;
            n.height = 1 + @max(lh, rh);
        }

        fn balance_factor(index: Index, arena: *Arena) i8 {
            var n = arena.get_node(index);
            const lh = @as(i8, @intCast(if (n.left) |i| arena.get_node(i).height else 0));
            const rh = @as(i8, @intCast(if (n.right) |i| arena.get_node(i).height else 0));
            return rh - lh;
        }

        fn get_child_index_ptr(index: Index, arena: *Arena, lateral: Lateral) *?Index {
            var n = arena.get_node(index);
            return switch (lateral) {
                .left => &n.left,
                .right => &n.right,
            };
        }

        fn rotate(index: Index, arena: *Arena, lateral: Lateral) void {
            var sub_index = get_child_index_ptr(index, arena, lateral.flip()).*.?;
            get_child_index_ptr(index, arena, lateral.flip()).* = get_child_index_ptr(sub_index, arena, lateral).*;
            get_child_index_ptr(sub_index, arena, lateral).* = sub_index;
            mem.swap(Node, arena.get_node(index), arena.get_node(sub_index));
            update_height(sub_index, arena);
            update_height(index, arena);
        }

        fn rebalance_if_needed(index: Index, arena: *Arena) void {
            update_height(index, arena);
            const heavy: Lateral = switch (balance_factor(index, arena)) {
                -2 => .left,
                2 => .right,
                else => return,
            };

            var sub_index = get_child_index_ptr(index, arena, heavy).*.?;
            var sub_bf = balance_factor(sub_index, arena);
            assert(sub_bf >= -1 and sub_bf <= 1);

            if ((sub_bf == -1 and heavy == .right) or (sub_bf == 1 and heavy == .left)) {
                rotate(sub_index, arena, heavy);
            }
            rotate(index, arena, heavy.flip());
        }

        const Node = struct {
            key: K,
            value: V,
            height: usize = 1,
            left: ?Index = null,
            right: ?Index = null,
            fn init(key: K, value: V) Node {
                return Node{ .key = key, .value = value };
            }
        };

        const Arena = struct {
            m: ArrayListUnmanaged(Metadata) = ArrayListUnmanaged(Metadata){},
            free_head: ?Index = null,
            const Self = @This();

            const Metadata = union(enum) {
                used: Node,
                free: ?Index,
            };

            const Entry = struct {
                index: Index,
                node_ptr: *Node,
            };

            fn init_capacity(allocator: Allocator, num: usize) !Arena {
                const m = try ArrayListUnmanaged(Metadata).initCapacity(allocator, num);
                return Arena{ .m = m };
            }

            fn create(self: *Arena, allocator: Allocator) !Entry {
                if (self.free_head) |index| {
                    var mdata: *Metadata = &self.m.items[@as(usize, @intCast(index))];
                    assert(mdata.* == .free);
                    self.free_head = mdata.free;
                    mdata.* = Metadata{ .used = undefined };
                    return Entry{
                        .index = index,
                        .node_ptr = &mdata.used,
                    };
                }
                try self.m.append(allocator, Metadata{ .used = undefined });
                const i = self.m.items.len - 1;
                return Entry{
                    .index = @as(Index, @intCast(i)),
                    .node_ptr = &self.m.items[i].used,
                };
            }

            fn destroy(self: *Arena, index: Index) void {
                var mdata = &self.m.items[@as(usize, @intCast(index))];
                assert(mdata.* == .used);
                mdata.* = Metadata{ .free = self.free_head };
                self.free_head = index;
            }

            fn get_node(self: *const Arena, index: Index) *Node {
                var mdata = &self.m.items[@as(usize, @intCast(index))];
                assert(mdata.* == .used);
                return &mdata.used;
            }
        };

        const KV = struct {
            key: K,
            value: V,
        };

        const GetOrPutResult = struct {
            value_ptr: *V,
            found_existing: bool,
        };

        pub fn init_capacity(allocator: Allocator, num: usize) !Self {
            const arena = try Arena.init_capacity(allocator, num);
            return Self{ .arena = arena };
        }

        pub fn deinit(self: *Self, allocator: Allocator) void {
            self.arena.m.deinit(allocator);
        }

        pub fn count(self: *Self) Index {
            return self.size;
        }

        pub fn contains(self: *Self, key: K) ?V {
            return self.get_ptr(key) != null;
        }

        pub fn get_ptr(self: *Self, key: K) ?*V {
            var index = self.root;
            while (index) |idx| {
                var node = self.arena.get_node(idx);
                switch (order_fn(key, node.key)) {
                    .lt => {
                        index = node.left;
                    },
                    .gt => {
                        index = node.right;
                    },
                    .eq => return &node.value,
                }
            }
            return null;
        }

        pub fn get(self: *Self, key: K) ?V {
            return if (self.get_ptr(key)) |ptr| ptr.* else null;
        }

        pub fn get_or_put(self: *Self, allocator: Allocator, key: K) !GetOrPutResult {
            var lat: Lateral = undefined;
            var par_index: ?Index = null;
            var index = self.root;
            while (index) |idx| {
                par_index = idx;
                var node = self.arena.get_node(idx);
                switch (order_fn(key, node.key)) {
                    .lt => {
                        index = node.left;
                        lat = .left;
                    },
                    .gt => {
                        index = node.right;
                        lat = .right;
                    },
                    .eq => return GetOrPutResult{ .value_ptr = &node.value, .found_existing = true },
                }
            }
            var e = try self.arena.create(allocator);
            e.node_ptr.* = Node.init(key, undefined);
            if (par_index) |idx| {
                var node = self.arena.get_node(idx);
                switch (lat) {
                    .left => node.left = e.index,
                    .right => node.right = e.index,
                }
            } else {
                self.root = e.index;
            }
            rebalance_if_needed(e.index, &self.arena);
            self.size += 1;
            return GetOrPutResult{ .value_ptr = &e.node_ptr.value, .found_existing = false };
        }

        pub fn put_no_clobber(self: *Self, allocator: Allocator, key: K, value: V) !void {
            var gop = try self.get_or_put(allocator, key);
            assert(!gop.found_existing);
            gop.value_ptr.* = value;
        }

        pub fn fetch_put(self: *Self, allocator: Allocator, key: K, value: V) !?V {
            var gop = try self.get_or_put(allocator, key);
            defer gop.value_ptr.* = value;
            if (gop.found_existing) return gop.value_ptr.*;
            return null;
        }

        pub fn put(self: *Self, allocator: Allocator, key: K, value: V) !void {
            var gop = try self.get_or_put(allocator, key);
            gop.value_ptr.* = value;
        }

        pub fn fetch_remove(self: *Self, key: K) ?V {
            return self._fetch_remove(&self.root, key);
        }

        fn _fetch_remove(self: *Self, index: *?Index, key: K) ?V {
            const idx = index.* orelse return null;
            const node = self.arena.get_node(idx);
            switch (order_fn(key, node.key)) {
                .lt => return self._fetch_remove(&node.left, key),
                .gt => return self._fetch_remove(&node.right, key),
                .eq => {},
            }
            defer {
                self.arena.destroy(idx);
                self.size -= 1;
            }
            blk: {
                if (node.left == null and node.right == null) {
                    index.* = null;
                    break :blk;
                }
                if (node.left != null and node.right == null) {
                    index.* = node.left;
                    break :blk;
                }
                if (node.left == null and node.right != null) {
                    index.* = node.right;
                    break :blk;
                }
                var i = &node.right;
                if (self.arena.get_node(i.*.?).left == null) {
                    self.arena.get_node(i.*.?).left = node.left;
                    index.* = i.*;
                    break :blk;
                }
                while (self.arena.get_node(i.*.?).left) |_| {
                    i = &self.arena.get_node(i.*.?).left;
                }
                const _right = self.arena.get_node(i.*.?).right;
                self.arena.get_node(i.*.?).left = node.left;
                self.arena.get_node(i.*.?).right = node.right;
                index.* = i.*;
                i.* = _right;
            }
            return node.value;
        }

        pub fn remove(self: *Self, key: K) bool {
            return self.fetch_remove(key) != null;
        }

        pub fn clone(self: *const Self, allocator: Allocator) !Self {
            const arena = Arena{
                .m = try self.arena.m.clone(allocator),
                .free_head = self.arena.free_head,
            };
            return Self{
                .arena = arena,
                .root = self.root,
                .size = self.size,
            };
        }

        pub fn to_owned_slice(self: *Self, allocator: Allocator) ![]KV {
            defer self.deinit(allocator);
            var m = ArrayListUnmanaged(KV){};
            try _to_owned_slice(allocator, &self.arena, &m, self.root);
            return try m.toOwnedSlice(allocator);
        }

        fn _to_owned_slice(allocator: Allocator, arena: *Arena, m: *ArrayListUnmanaged(KV), index: ?Index) !void {
            const idx = index orelse return;
            const n = arena.get_node(idx);
            try _to_owned_slice(allocator, arena, m, n.left);
            try m.append(allocator, KV{ .key = n.key, .value = n.value });
            try _to_owned_slice(allocator, arena, m, n.right);
        }

        fn walk(self: *Self) void {
            self._walk(self.root);
        }

        fn _walk(self: *Self, index: ?Index) void {
            const idx = index orelse return;
            const node = self.arena.get_node(idx);
            self._walk(node.left);

            print("{{ ", .{});
            print("key: {any}, ", .{node.key});
            print("val: {any}, ", .{node.value});

            if (node.left) |i| {
                print("l: {}, ", .{self.arena.get_node(i).key});
            } else {
                print("l: _, ", .{});
            }

            if (node.right) |i| {
                print("r: {}", .{self.arena.get_node(i).key});
            } else {
                print("r: _", .{});
            }

            print(" }}\n", .{});
            self._walk(node.right);
        }
    };
}

test "basic" {
    // if (true) return error.SkipZigTest;

    const allocator: Allocator = testing.allocator;

    var tree = AvlTreeUnmanaged(i32, u8, asc(i32)){};
    defer tree.deinit(allocator);

    _ = try tree.put(allocator, 6, 'a');
    _ = try tree.put(allocator, 2, 'b');
    _ = try tree.put(allocator, 11, 'c');
    _ = try tree.put(allocator, 11, 'd');
    _ = try tree.put(allocator, 8, 'e');
    _ = try tree.put(allocator, 20, 'f');
    _ = try tree.put(allocator, 6, 'g');

    try testing.expect(tree.count() == 5);
    try testing.expect(tree.get(6) == 'g');
    try testing.expect(tree.get(2) == 'b');
    try testing.expect(tree.get(11) == 'd');
    try testing.expect(tree.get(8) == 'e');
    try testing.expect(tree.get(20) == 'f');
}

test "duplicated key" {
    // if (true) return error.SkipZigTest;

    const allocator: Allocator = testing.allocator;

    const order_fn = struct {
        fn f(a: i32, b: i32) math.Order {
            return switch (math.order(a, b)) {
                .eq => .lt,
                else => |x| x,
            };
        }
    }.f;

    var tree = AvlTreeUnmanaged(i32, []const u8, order_fn){};
    defer tree.deinit(allocator);

    _ = try tree.put_no_clobber(allocator, 6, "a");
    _ = try tree.put_no_clobber(allocator, 2, "b");
    _ = try tree.put_no_clobber(allocator, 11, "c");
    _ = try tree.put_no_clobber(allocator, 11, "d");
    _ = try tree.put_no_clobber(allocator, 8, "e");
    _ = try tree.put_no_clobber(allocator, 20, "f");
    _ = try tree.put_no_clobber(allocator, 6, "g");

    try testing.expect(tree.count() == 7);
}

test "example random" {
    // if (true) return error.SkipZigTest;

    const Rand = struct {
        var rand: u64 = undefined;
        fn get(lo: u64, hi: u64) !u64 {
            try std.os.getrandom(std.mem.asBytes(&rand));
            return (rand % (hi - lo)) + lo;
        }
    };

    const allocator = testing.allocator;

    for (0..100) |_| {
        var tree = try AvlTree(u32, void, asc(u32)).init(allocator);
        defer tree.deinit();

        var tester = Tester(u32, void, asc(u32)).init(allocator, &tree);
        defer tester.deinit();

        const N = @as(usize, @intCast(try Rand.get(15, 32)));
        for (0..N) |i| {
            const key = @as(u32, @intCast(try Rand.get(0, 15)));

            if (i % 4 == 3) {
                tester.remove(key);
            } else {
                try tester.put(key, {});
            }
        }

        try tester.test_tree();
    }

    for (0..100) |_| {
        var tree = try AvlTree(u32, void, desc(u32)).init(allocator);
        defer tree.deinit();

        var tester = Tester(u32, void, desc(u32)).init(allocator, &tree);
        defer tester.deinit();

        const N = @as(usize, @intCast(try Rand.get(15, 32)));
        for (0..N) |i| {
            const key = @as(u32, @intCast(try Rand.get(0, 15)));

            if (i % 4 == 3) {
                tester.remove(key);
            } else {
                try tester.put(key, {});
            }
        }
        try tester.test_tree();
    }
}

fn Tester(comptime K: type, comptime V: type, comptime order_fn: fn (K, K) math.Order) type {
    return struct {
        hm: std.AutoArrayHashMap(K, V),
        tree: *AvlTree(K, V, order_fn),
        allocator: Allocator,
        const Self = @This();

        fn init(allocator: Allocator, tree: *AvlTree(K, V, order_fn)) Self {
            const hm = std.AutoArrayHashMap(K, void).init(allocator);
            return Self{ .hm = hm, .tree = tree, .allocator = allocator };
        }

        fn deinit(self: *Self) void {
            self.hm.deinit();
        }

        fn put(self: *Self, key: K, value: V) !void {
            _ = try self.tree.put(key, value);
            try self.hm.put(key, value);
        }

        fn remove(self: *Self, data: K) void {
            _ = self.tree.remove(data);
            _ = self.hm.orderedRemove(data);
        }

        fn test_tree(self: *Self) !void {
            var cloned = try self.tree.clone();
            const slice = try cloned.to_owned_slice();

            defer self.allocator.free(slice);
            const Context = struct {
                keys: []u32,
                pub fn lessThan(ctx: @This(), a_index: usize, b_index: usize) bool {
                    const a = ctx.keys[a_index];
                    const b = ctx.keys[b_index];
                    return order_fn(b, a) == .lt;
                }
            };
            self.hm.sort(Context{ .keys = self.hm.keys() });

            for (slice) |kv| {
                const x = self.hm.pop();
                try testing.expectEqual(kv.key, x.key);
                try testing.expectEqual(kv.value, x.value);
            }

            try self.test_balance_factor();
        }

        fn test_balance_factor(self: *Self) !void {
            try _test_balance_factor(&self.tree.unmanaged.arena, self.tree.unmanaged.root);
        }

        fn _test_balance_factor(arena: *AvlTree(K, V, order_fn).Unmanaged.Arena, index: ?AvlTree(K, V, order_fn).Index) !void {
            const idx = index orelse return;
            const bf = AvlTree(K, V, order_fn).Unmanaged.balance_factor(idx, arena);
            try testing.expect(bf >= -1 and bf <= 1);
            try _test_balance_factor(arena, arena.get_node(idx).left);
            try _test_balance_factor(arena, arena.get_node(idx).right);
        }
    };
}
