# POPL 2027 Blind Submission Package

This directory contains the anonymized submission bundle for the POPL 2027 paper.

Contents:

- `main.tex`: anonymized manuscript source
- `references.bib`: anonymized bibliography
- `main.pdf`: compiled submission PDF, created after building
- `supplement/`: anonymized Lean proof scripts and project files

Build the paper PDF with:

```bash
latexmk -g -lualatex main.tex
```

The supplementary Lean project can be checked with:

```bash
cd supplement
lake build
```
