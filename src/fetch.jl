# Fetching the OpenSymbolicRules data.
#
# The rules are not shipped with the package: they are downloaded on first use from
# GitHub, as a tarball of a branch, tag or commit, and kept in a Scratch.jl space, one
# directory per ref. The OpenSymbolicRules repositories are under active development,
# so the default ref is the main branch; `update_rules!` downloads it again.
#
# For work on the rules themselves, the environment variable SYMJOSR_INTEGRATION_DIR
# (or `use_rules_dir!`) points at a local checkout, which is used as is.

const INTEGRATION_REPO = "OpenSymbolicRules/Integration"
const DEFAULT_REF = Ref("main")
const _LOCAL_DIR = Ref{Union{Nothing,String}}(nothing)

_refdir(ref) = replace(ref, r"[^A-Za-z0-9._-]" => "_")

"""
    use_rules_dir!(dir)
    use_rules_dir!(nothing)

Use the OpenSymbolicRules Integration checkout in `dir` instead of a download; `nothing`
goes back to downloading. Loaded rule sets are dropped.
"""
function use_rules_dir!(dir)
    dir === nothing || isfile(joinpath(dir, "rules", "meta.json")) ||
        throw(ArgumentError("$dir has no rules/meta.json: not an Integration checkout"))
    _LOCAL_DIR[] = dir
    empty!(_RULESETS)
    nothing
end

"""
    rules_dir(; ref = SymJOSR.DEFAULT_REF[], update = false)

The directory of an OpenSymbolicRules Integration tree, downloaded if need be. A local
checkout set with [`use_rules_dir!`](@ref) or `ENV["SYMJOSR_INTEGRATION_DIR"]` wins.
"""
function rules_dir(; ref::AbstractString = DEFAULT_REF[], update::Bool = false)
    _LOCAL_DIR[] !== nothing && return _LOCAL_DIR[]
    d = get(ENV, "SYMJOSR_INTEGRATION_DIR", "")
    isempty(d) || return d
    dir = joinpath(Scratch.@get_scratch!("integration"), _refdir(ref))
    if update || !isfile(joinpath(dir, "rules", "meta.json"))
        _download_tree(ref, dir)
    end
    dir
end

function _download_tree(ref, dir)
    url = "https://codeload.github.com/$INTEGRATION_REPO/tar.gz/$ref"
    @info "SymJOSR: downloading OpenSymbolicRules Integration ($ref)"
    tmp = mktempdir()
    tgz = Downloads.download(url, joinpath(tmp, "rules.tar.gz"))
    out = joinpath(tmp, "x")
    open(tgz) do io
        Tar.extract(CodecZlib.GzipDecompressorStream(io), out)
    end
    top = only(readdir(out; join = true))       # Integration-<ref>/
    isdir(dir) && rm(dir; recursive = true)
    mkpath(dirname(dir))
    mv(top, dir)
    sha = _remote_sha(ref)
    sha === nothing || write(joinpath(dir, ".symjosr-sha"), sha)
    rm(tmp; recursive = true, force = true)
    dir
end

function _remote_sha(ref)
    try
        io = IOBuffer()
        Downloads.request("https://api.github.com/repos/$INTEGRATION_REPO/commits/$ref";
            output = io, headers = ["Accept" => "application/vnd.github.sha"])
        s = strip(String(take!(io)))
        occursin(r"^[0-9a-f]{40}$", s) ? s : nothing
    catch
        nothing
    end
end

"""
    rules_version()

Where the loaded rules came from: the directory, and the commit when it is known.
"""
function rules_version()
    dir = rules_dir()
    f = joinpath(dir, ".symjosr-sha")
    sha = isfile(f) ? read(f, String) :
        isdir(joinpath(dir, ".git")) ? _git_head(dir) : nothing
    (dir = dir, commit = sha)
end
_git_head(dir) = try readchomp(`git -C $dir rev-parse HEAD`) catch; nothing end

"""
    update_rules!(; ref = SymJOSR.DEFAULT_REF[])

Download the rules again (for a branch, its latest commit) and drop loaded rule sets.
"""
function update_rules!(; ref::AbstractString = DEFAULT_REF[])
    rules_dir(; ref, update = true)
    empty!(_RULESETS)
    rules_version()
end
