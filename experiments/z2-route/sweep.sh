#!/usr/bin/env bash
# sweep.sh BIN s delta floor r1 r2 budget secs
# Covers each pattern of `zruns` in its own process (`zruns ... at i`: plain
# z_floor cover, then the q-lift if the plain cover leaves a region open)
# under `timeout secs`; one line per pattern, then a summary.
set -u
[ $# -eq 8 ] || { echo "usage: $0 BIN s delta floor r1 r2 budget secs" >&2; exit 2; }
bin=$1; s=$2; d=$3; floor=$4; r1=$5; r2=$6; budget=$7; secs=$8
n=$("$bin" "$s" "$d" "$floor" "$r1" "$r2" "$budget" count) || exit 1
declare -A tally=([closed-by-plain]=0 [closed-by-qlift]=0 [open]=0 [timeout]=0 [error]=0)
for ((i = 0; i < n; i++)); do
    t0=$SECONDS
    out=$(timeout "$secs" "$bin" "$s" "$d" "$floor" "$r1" "$r2" "$budget" at "$i" 2>&1)
    rc=$?
    pat=$(sed -n 's/^PATTERN //p' <<<"$out")
    # one stage line per finished cover: "plain|qlift closed|OPEN <pattern> regions R open O budget B secs T"
    stages=$(sed -n 's/^    \(plain\|qlift\) .* regions \([0-9]*\)  *open \([0-9]*\)  *budget \([A-Za-z]*\)  *secs \([0-9]*\)$/\1: regions=\2 open=\3 budget=\4 secs=\5/p' <<<"$out" | paste -sd ';' -)
    case $(sed -n 's/^VERDICT //p' <<<"$out") in
        plain) what=closed-by-plain ;;
        qlift) what=closed-by-qlift ;;
        open) what=open ;;
        *) if [ $rc -eq 124 ]; then what=timeout; else what=error; stages="rc=$rc: $(tail -1 <<<"$out")"; fi ;;
    esac
    tally[$what]=$((tally[$what] + 1))
    # a timeout with no stage line was still in the plain cover
    [ "$what" = timeout ] && stages="${stages:+$stages;}$([ -z "$stages" ] && echo plain || echo qlift): killed"
    printf '%3d  %-16s %-24s %4ds  %s\n' "$i" "$what" "${pat:-?}" $((SECONDS - t0)) "$stages"
done
echo "summary s=$s delta=$d floor=$floor runs<=$r1,$r2 budget=$budget timeout=${secs}s: patterns $n, closed-by-plain ${tally[closed-by-plain]}, closed-by-qlift ${tally[closed-by-qlift]}, open ${tally[open]}, timeout ${tally[timeout]}, error ${tally[error]}"
