# ThunderMonkey

2024 年全国大学生计算机系统能力大赛-编译系统设计赛-编译系统实现赛，北京大学“一梦全能”队伍 ARM 赛道编译器。

ThunderMonkey 编译器由三部分构成：

- “Zvezda”（Звезда，“星辰”），预处理器与前端
- “Chollima”（천리마，“千里马”），中间表示
- “Hyoksin”（혁신，“革新”），汇编生成器

除 Rust 标准库外，我们使用的库还有：

- [`pest`](https://github.com/pest-parser/pest)，一个基于解析表达式文法的解析器生成器。同时依赖 `pest_derive`。Apache-2.0 或 MIT licenses 许可证。
- [`libc`](https://github.com/rust-lang/libc)，Rust 官方提供的与 C 互操作的工具库。Apache-2.0 或 MIT licenses 许可证。
- [`rustc_hash`](https://github.com/rust-lang/rustc-hash)，Rust 官方提供的一种哈希表，相比 Rust 标准库的哈希算法，`rustc_hash` 更加快速，但抗碰撞能力稍弱。Apache-2.0 或 MIT licenses 许可证。
- [`genawaiter`](https://github.com/whatisaphone/genawaiter)，无栈携程库。Apache-2.0 或 MIT 许可证。

## 主要数据结构

### 抽象语法树

语法树的根是 `TranslationUnit`（翻译单元），`TranslationUnit` 实质上是由 `Definition`（符号定义）构成的列表。`Definition` 是一个元组，包含符号的*标识符*、*初始化器*和符号的*类型*。

*初始化器*是一个 Rust 枚举，分为：

1. `Function(Block, is_entry, arg_handlers)`（函数），其中 `arg_handlers` 记录了各个参数的 `handler`，`Block` 存储了函数体；
2. `Expr(Expr)`（表达式）；
3. `ConstInt(i32)` 和 `ConstFloat(f32)`（常量）；
4. `List(InitList)`（初始化列表）；
5. `ConstList(ConstInitList)`（常量初始化列表）。


*类型*也是一个枚举，分为

1. `Int`（整型）；
2. `FLoat`（浮点型）；
3. `Void`（空）；
4. `Pointer(Type, Vec<usize>)`（指针），`Vec<usize>` 存储了各个维度的长度；
5. `Array(Type, Vec<usize>)`（数组），`Vec<usize>` 存储了各个维度的长度；
6. `Function(Box<Type>, Vec<Type>)`（函数），`Box<Type>` 存储返回值类型，而 `Vec<Type>` 存储各个参数的类型；
7. `VAList`，变参函数的参数列表，为 `putf` 保留。


初始化器和类型**共同决定**了一个符号。例如：

- `int a;` 定义的符号 `a`
    - 初始化器为 `None`
    - 类型为 `Int`
- `int a = 1;` 定义的符号 `a`
    - 初始化器为 `Expr(1)`
    - 类型为 `Int`
- `const int a = 1;` 定义的符号 `a`
    - 初始化器为 `Const(1)`
    - 类型为 `Int`
- `int a[2][1] = {{1}, {2}};` 定义的符号 `a`
    - 初始化器为 `List(InitList([InitList([Expr(1)]), InitList([Expr(2)])]))`
    - 类型为 `Array(Int, [2, 1])`
- `const int a[2][1] = {{1}, {2}};` 定义的符号 `a`
    - 初始化器为 `ConstList(ConstInitList([ConstInitList([1]), ConstInitList([2])]))`
    - 类型为 `Array(Int, [2, 1])`
- 函数**定义** `int f(int a) { return 0; }` 定义的符号 `main`
    - 初始化器为 `Function(["a"], Block([Return(0)]))`
    - 类型为 `Function(Int, [Int])`

实际实现中，初始化器和类型并不存储在 `Definition` 的内部，而是存储在一个哈希表中；`Definition` 仅存储指向哈希表的 `Handler`。

`Block`（复合语句）是语法树的基础。`Block` 是由一系列元素组成的列表，这些列表可以是：

1. `Definition`（局部变量定义）；
2. `Statement`（语句，即表达式（`Expr`）、`if`、`while`、`continue` 和 `break`）；
3. `Block（复合语句），`Block` 套 `Block` 是很正常的。

`Expr`（表达式）是语法树的核心，仅摘录一部分：

```rust
pub enum ExprInner {
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    // ......
    Num(i32),
    Var(String),
    Func(String, Vec<Expr>),
    Array(String, Vec<Expr>, bool),
}
```

## Zvezda

### 预处理器

Zvezda 在预处理器部分负责：

1. 换行符替换，`\r\n`、`\r` 统一替换为 `\n`
2. 行拼接，根据 C 语言标准，凡在反斜杠出现于行尾（紧跟换行符）时，删除反斜杠和换行符，把两个物理源码行组合成一个逻辑源码行。**这属于我们对 SysY 的扩展，而不是标准 SysY**。例如：

```c
int main() {
    int a = 1; // \
    int b;
    int b;     // \\\\
    int b;
    return a;
}
```

被处理为：

```c
int main() {
    int a = 1; //     int b;
    int b;     // \\\    int b;
    return a;
}
```

3. 去除注释，预处理器按照 C 语言标准去除注释。

### 解析器

#### 第一次解析

第一次解析中，使用 pest 将代码处理为语法树。因为 pest 设计上的局限性，此处语法树使用的是 pest 中 `Pairs<Rule>` 的形式。此外，这里还没有对运算符优先级做处理，表达式仍然表现为 `Pair` 流的形式。

#### 第二次解析

遍历上述 `Pairs<Rule>` 的语法树，转换为 `TranslationUnit`。同时，在这一步使用 pest 提供的 `PrattParser<Rule>` 处理运算符优先级。

#### 语义检查

遍历 `TranslationUnit`，进行语义检查和常量表达式计算。

为支持作用域嵌套，ThunderMonkey 的符号表设计为一个栈（`Vec<HashMap<String, Definition>>`），在查找符号时，优先查找作用域最靠内的符号。

## Chollima

Chollima 是一种简单的、基于栈的中间表示。例如，`x = x / 10.0;` 编译为：

```
load_addr x
load_addr x
load
push_float 10.0
div_float
store
```

全部 Chollima 指令如下：

## 算数与位运算指令

- `add_int`：从栈顶依次弹出整数 `b`、`a`，计算和 `a + b`，并压栈。
- `sub_int`：从栈顶依次弹出整数 `b`、`a`，计算差 `a - b`，并压栈。
- `mul_int`：从栈顶依次弹出整数 `b`、`a`，计算积 `a * b`，并压栈。
- `div_int`：从栈顶依次弹出整数 `b`、`a`，计算商 `a / b`，并压栈。

以上指令的结果均为整数。

- `add_float`：从栈顶依次弹出浮点数 `b`、`a`，计算和 `a + b`，并压栈。
- `sub_float`：从栈顶依次弹出浮点数 `b`、`a`，计算差 `a - b`，并压栈。
- `mul_float`：从栈顶依次弹出浮点数 `b`、`a`，计算积 `a * b`，并压栈。
- `div_float`：从栈顶依次弹出浮点数 `b`、`a`，计算商 `a / b`，并压栈。

以上指令的结果均为浮点数。

- `mod_int`：从栈顶依次弹出整数 `b`、`a`，计算模 `a % b`，并压栈。
- `sll`：从栈顶依次弹出整数 `b`、`a`，计算逻辑左移 `a << b`，并压栈。
- `slr`：从栈顶依次弹出整数 `b`、`a`，计算逻辑右移 `a >> b`，并压栈。
- `sar`：从栈顶依次弹出整数 `b`、`a`，计算算数左移 `a >> b`，并压栈。
- `and`：从栈顶依次弹出整数 `b`、`a`，计算按位与 `a & b`，并压栈。
- `or`：从栈顶依次弹出整数 `b`、`a`，计算按位或 `a | b`，并压栈。
- `xor`：从栈顶依次弹出整数 `b`、`a`，计算按位异或 `a ^ b`，并压栈。

以上指令的结果均为整数。

## 比较运算指令

- `eq_int`：从栈顶依次弹出整数 `b`、`a`，比较 `a == b`，并将比较结果压栈。
- `ne_int`：从栈顶依次弹出整数 `b`、`a`，比较 `a != b`，并将比较结果压栈。
- `le_int`：从栈顶依次弹出整数 `b`、`a`，比较 `a <= b`，并将比较结果压栈。
- `lt_int`：从栈顶依次弹出整数 `b`、`a`，比较 `a < b`，并将比较结果压栈。
- `ge_int`：从栈顶依次弹出整数 `b`、`a`，比较 `a >= b`，并将比较结果压栈。
- `gt_int`：从栈顶依次弹出整数 `b`、`a`，比较 `a > b`，并将比较结果压栈。

以上指令的结果均为整数，且一定为 `0` 或 `1`。

- `eq_float`：从栈顶依次弹出浮点数 `b`、`a`，比较 `a == b`，并将比较结果压栈。
- `ne_float`：从栈顶依次弹出浮点数 `b`、`a`，比较 `a != b`，并将比较结果压栈。
- `le_float`：从栈顶依次弹出浮点数 `b`、`a`，比较 `a <= b`，并将比较结果压栈。
- `lt_float`：从栈顶依次弹出浮点数 `b`、`a`，比较 `a < b`，并将比较结果压栈。
- `ge_float`：从栈顶依次弹出浮点数 `b`、`a`，比较 `a >= b`，并将比较结果压栈。
- `gt_float`：从栈顶依次弹出浮点数 `b`、`a`，比较 `a > b`，并将比较结果压栈。

以上指令的结果均为整数，且一定为 `0` 或 `1`。

### 栈操纵指令

- `push_int <imm>`：将整数 `imm` 压入栈顶。
- `push_float <imm>`：将浮点数 `imm` 压入栈顶。

- `pop_words <n>`：从栈顶弹出 `n` 个字。
- `double`：从栈顶弹出 1 个字，并将它重复两次压入栈顶。

以上指令中，一个字为 32 位。

### 类型转换指令

- `cvt_i_f`：从栈顶弹出一个整数，将其转换为浮点数，并压栈。
- `cvt_f_i`：从栈顶弹出一个浮点数，将其转换为整数，并压栈。

### 转移指令

#### 条件与无条件转移指令

- `br <label_1>, <label_2>`：从栈顶弹出一个整数，与 0 比较。如果与 0 比较不等，则转移至 `label_1`，否则转移至 `label_2`
- `jmp <label>`：无条件转移至 `label`。

#### 函数调用指令

- `call_int <func>, <n>`：以 `n` 个参数调用函数 `func`，期望它返回的字是一个整数。将这个字压栈。如果这个函数返回的字是浮点数，或没有返回值，是未定义行为。
- `call_float <func>, <n>`：以 `n` 个参数调用函数 `func`，期望它返回的字是一个浮点数。将这个字压栈。如果这个函数返回的字是整数，或没有返回值，是未定义行为。
- `call_void <func>, <n>`：以 `n` 个参数调用函数 `func`，期望它没有任何返回值。即便有返回值，也将丢弃。

注意，函数调用前需保证 `n` 个参数从右向左压栈。这里的“栈”指虚拟机栈，而非真实的栈。有关调用约定请见后文。

#### 函数返回指令

- `ret_int`：无条件返回至当前函数的调用者。期望当前函数返回的字是一个整数，或没有返回值。如果当前函数返回的字是浮点数，是未定义行为。
- `ret_float`：无条件返回至当前函数的调用者。期望当前函数返回的字是一个浮点数。如果当前函数返回的字是整数，或没有返回值，是未定义行为。

### 内存操纵指令

- `load_addr <var>`：将变量 `var` 的地址加载到栈顶。
- `load`：从栈顶弹出一个字 `p`，将 `p` 视为一个指针，将 `p` 指向的字压入栈顶。
- `store`：从栈顶依次弹出两个字 `d`、`p`，将 `p` 视为一个指针，将 `d` 存储在 `p` 指向的字。

### 标签

- `label_<label>`：IR 中的标签。

### 其它指令

- `start_time <lineno>` 和 `stop_time <lineno>`：专用于 `starttime()` 和 `stoptime()` 函数的 Chollima 指令。

以上“整数”指 32 位补码表示的有符号整数，“浮点数”指 IEEE-754 Binary 32 浮点数。Chollima 假定目标机器的指针宽度为 32 位。除此之外，Chollima 没有更多约束。

## IR 生成

在生成表达式的 IR 时，SysY 中的表达式被进一步分为三类：

1. 左值表达式（lvalue），这种表达式在 Chollima 栈顶压入一个内存地址。例如，语句 `x = 1;` 中的 `x` 是左值表达式。
2. 右值表达式（rvalue），这种表达式在 Chollima 栈顶压入一个字。例如，`x = y;` 中的 `y` 是右值表达式
3. 弃值表达式（dvalue），这种表达式仅进行副作用，不改变 Chollima 栈。例如，语句 `x = 1;` 中的 `x = 1` 是弃值表达式，这个语句只会执行赋值的副作用而改变 Chollima 栈。

## Hyoksin

Hyoksin 对 Chollima 模式匹配。例如，`add_int` 会被编译为：

```asm
pop {r1}
pop {r0}
add r0, r0, r1
push {r0}
```

而 `add_float` 会被编译为：

```
pop {r1}
pop {r0}
mov32 r2, __aeabi_fadd
blx r2
push {r0}
```

这里，`mov32` 是一个汇编宏，其定义为：

```asm
.macro mov32, reg, val
    movw \reg, #:lower16:\val
    movt \reg, #:upper16:\val
.endm
```
### 调用约定

简单起见，ThunderMonkey 使用了非标准的调用约定：所有参数均通过栈传递，从右向左压栈。

特别地，在调用 SysY 运行时库函数时，前四个参数（如果有），将位于 `r0`、`r1`、`r2` 和 `r3` 寄存器。其余参数从右向左压栈。

为与 SysY 运行时库一致，ThunderMonkey 以 `r7` 为帧指针，而非传统的 `r11`。
