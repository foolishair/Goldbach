# Goldbach 独立 Lean 子项目

[![Build](https://github.com/foolishair/Goldbach/actions/workflows/build.yml/badge.svg)](https://github.com/foolishair/Goldbach/actions/workflows/build.yml)
[![Lean 4.29.0](https://img.shields.io/badge/Lean-4.29.0-blueviolet)](https://leanprover-community.github.io/)
[![mathlib v4.29.0](https://img.shields.io/badge/mathlib-v4.29.0-orange)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

> 这是从 PrimeNumberTheoremAnd 项目脱离出来的独立 Lake 项目，
> 只依赖 mathlib4，不依赖 PNT 任何模块。

## 结构

```
goldbach/
├── lakefile.toml          ← 项目定义（require mathlib v4.29.0）
├── lean-toolchain         ← 锁定 Lean 4.29.0
├── lake-manifest.json     ← 依赖 manifest（从 PNT 拷贝）
├── .lake/packages         ← symlink → PNT 的 packages（复用 145MB mathlib + 8232 .olean cache）
├── Goldbach.lean          ← root module (import Goldbach.Statements)
└── Goldbach/
    └── Statements.lean    ← 主源文件（21 真定理 / 0 sorry）
```

## 独立 build

```bash
export PATH="/c/Users/fzq/.elan/bin:$PATH"
cd c:/Project/MathResearch/experiments/lean/goldbach
lake build                # → Build completed successfully (2201 jobs)
```

## 关键技巧：复用 PNT 的 mathlib cache

不重新下 mathlib，直接软链到 PNT 已有的 packages：

```bash
mkdir -p .lake
cd .lake
ln -s /c/Project/MathResearch/experiments/lean/PrimeNumberTheoremAnd/.lake/packages packages
```

省 145MB mathlib clone + 8232 mathlib .olean 重下（cache get）。
所有 .olean 都从 PNT cache 命中，goldbach 自己只编译 Goldbach.lean / Statements.lean
两个文件（47 秒）。

## 已证 21 真定理（0 sorry / 0 警告）

完整清单见 `../README.md`。核心包括：

- north star: `StrongGoldbach` / `WeakGoldbach` / `HardyLittlewoodAsymptotic`
- 计数: `goldbachCount n`（r(n) 形式化）
- 真定理: `strong_implies_weak`、`hl_implies_strong_large`、
  `goldbachCount_pos_iff`、`goldbach_decomp_parity` 等

## 与上游 PNT 的关系

- 不依赖 PNT 任何模块（mathlib only）
- 可以独立 PR / 独立发布
- 如果 PNT 更新 mathlib 版本，本项目跟着改 lakefile 的 rev 即可
