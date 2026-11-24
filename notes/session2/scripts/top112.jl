# time SymJOSR's top-level SymJ calls on their own, as precompiling runs them
using SymJ
flush(stdout)
for (name, f) in [
        ("Sym(:x)", () -> Sym(:𝓍)),
        ("SymJ.PI", () -> SymJ.PI),
        ("Sym(im)", () -> Sym(im)),
        ("Sym(eulergamma)", () -> Sym(Base.MathConstants.eulergamma)),
        ("Sym(Inf)", () -> Sym(Inf)),
        ("SymJ.ONE * Sym(2)", () -> SymJ.ONE * Sym(2)),
    ]
    t = time(); f(); println(rpad(name, 22), round(time() - t, digits = 2), " s"); flush(stdout)
end
