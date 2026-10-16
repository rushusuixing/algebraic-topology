# algebraic-universal-coefficient-theorem

## English

The algebraic universal coefficient theorem for homology, a subproject of [algebraic-topology](../README.md).

Let R be a PID, C a degreewise free ℤ-indexed chain complex of R-modules, and D any R-module. The formalization proves the short exact sequence

$$
0 \longrightarrow H_n(C)\otimes_R D
\longrightarrow H_n(C\otimes_R D)
\longrightarrow \operatorname{Tor}_1^R(H_{n-1}(C),D)
\longrightarrow 0.
$$

This sequence admits a splitting, yielding a noncanonical direct sum isomorphism. No finite rank assumption is required, and D need not be free or flat.
The code uses Mathlib's standard `Tor'`, derived in the first variable.

Main file: [AlgebraicUCT.lean](UniversalCoefficient/AlgebraicUCT.lean).
Main declarations: `algebraic_uct`, `algebraicUCT_shortExact`, `algebraicUCTSplitting`, and `algebraicUCTDirectSumIso`.

After installing [Lean/Elan](https://leanprover-community.github.io/get_started.html) and Git, run:

```sh
git clone https://github.com/rushusuixing/algebraic-topology.git
cd algebraic-topology/algebraic-universal-coefficient-theorem
lake exe cache get
lake build
lake env lean Audit.lean
```

`lean-toolchain` and `lake-manifest.json` pin Lean v4.35.0-rc4 and the Mathlib revision.
Lake fetches the dependencies; `.lake/` is excluded from version control.

CI builds the project in an independent environment and runs `python3 scripts/check_axioms.py` to check the transitive axioms of the four main declarations.
The allowed standard axioms are `propext`, `Classical.choice`, and `Quot.sound`; the check fails on `sorryAx` or any other axiom.
The current formalization establishes the short exact sequence and existence of a splitting. Naturality of the sequence has not been formalized.

## 中文

代数同调泛系数定理，是 [algebraic-topology](../README.md) 的子项目。

设 R 为 PID，C 为逐阶自由的 ℤ 分次链复形，D 为任意 R-模。已证明短正合列

$$
0 \longrightarrow H_n(C)\otimes_R D
\longrightarrow H_n(C\otimes_R D)
\longrightarrow \operatorname{Tor}_1^R(H_{n-1}(C),D)
\longrightarrow 0.
$$

该列存在分裂，并给出非规范直和同构。不要求有限秩，也不限制 D 自由或平坦。
代码使用 Mathlib 对第一变量导出的标准 `Tor'`。

主文件：[AlgebraicUCT.lean](UniversalCoefficient/AlgebraicUCT.lean)。
主声明：`algebraic_uct`、`algebraicUCT_shortExact`、`algebraicUCTSplitting`、`algebraicUCTDirectSumIso`。

安装 [Lean/Elan](https://leanprover-community.github.io/get_started.html) 和 Git 后运行：

```sh
git clone https://github.com/rushusuixing/algebraic-topology.git
cd algebraic-topology/algebraic-universal-coefficient-theorem
lake exe cache get
lake build
lake env lean Audit.lean
```

`lean-toolchain` 和 `lake-manifest.json` 固定 Lean v4.35.0-rc4 及 Mathlib 版本。
依赖由 Lake 获取，`.lake/` 不纳入版本控制。

CI 在独立环境构建项目，并运行 `python3 scripts/check_axioms.py` 检查四个主声明的传递公理。
允许的标准公理为 `propext`、`Classical.choice`、`Quot.sound`；遇到 `sorryAx` 或其他公理会失败。
当前证明包括短正合与分裂存在，不包含主序列自然性的形式化。

## License

Copyright 2026 rushusuixing. Licensed under Apache-2.0; see [LICENSE](../LICENSE) and [NOTICE](../NOTICE).
