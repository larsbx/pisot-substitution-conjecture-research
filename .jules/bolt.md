## 2024-05-19 - EAFP dictionary lookups
**Learning:** Python's EAFP (Easier to Ask for Forgiveness than Permission) pattern using `try...except KeyError` is measurably faster than explicit dictionary presence checks (`if key not in dict`) combined with `itertools.chain.from_iterable()` inside tight substitution application loops.
**Action:** Use `try...except KeyError` around dict accesses in inner loops instead of double-lookups.
