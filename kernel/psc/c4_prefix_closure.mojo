"""Complete bounded prefix windows and their literal parent/local addresses.

A certificate binds sigma, the actual block substitution tau = sigma^k,
a nonempty seed U with U a proper prefix of tau(U), and consecutive complete
windows tau^r(U).  These finite premises can feed the separate Lean limit
construction.  The packet is not a serialization or construction of an
infinite word, a compact tile, or a compact-overlap measure.

Every source position and every local full Mark survives.  Source and target
words are stored in full, so their before/selected/after splits are determined
without storing a quadratic number of repeated global prefixes.  Local Marks
are stored explicitly.  Terminal cuts are recorded but are not occurrences.

The strict-growth and resource restrictions are constructor restrictions;
they do not assert that nongrowing substitutions lack infinite fixed words.
The pre-code gate is docs/c4-prefix-closure-literature-2026-11-11.md.
"""

from finite_linear_algebra.integer_matrix import matmul
from finite_linear_algebra.integer_vector import add, matvec
from substitution_dynamics.substitution import Substitution, validate_word
from psc.words import parikh
from psc.c4_nonunit_residue_occupancy import checked_substitution, same_vector
from psc.c4_madic_residue import build_madic_residue, residue_class, residue_fixture_images

comptime PREFIX_IMAGE_CAP = 3
comptime PREFIX_PERIOD_CAP = 3
comptime PREFIX_GENERATION_CAP = 3
comptime PREFIX_SEED_CAP = 32
comptime PREFIX_WORD_CAP = 4096
comptime PREFIX_OCCURRENCE_CAP = 12288


struct PrefixTransition(Copyable, Movable):
    var generation: Int
    # All N+1 cuts, including the terminal cut:
    # [parentOrdinal,globalBoundary,sourcePrefix3,expandedPrefix3].
    var cuts: List[List[Int]]
    # [parentOrdinal,parentLetter,markID,localIndex,globalIndex,selected,
    #  sourcePrefix3,transport3,localPrefix3,globalPrefix3].
    var occurrences: List[List[Int]]

    def __init__(out self, generation: Int):
        self.generation = generation
        self.cuts = List[List[Int]]()
        self.occurrences = List[List[Int]]()


struct PrefixClosure(Copyable, Movable):
    var images: List[List[Int]]
    var period: Int
    var generations: Int
    var seed: List[Int]
    var word_cap: Int
    var occurrence_cap: Int
    var matrix: List[Int]
    var block_images: List[List[Int]]
    var block_matrix: List[Int]
    # [parentLetter,localIndex,selected,localPrefix3,localSuffix3].
    var marks: List[List[Int]]
    var mark_before: List[List[Int]]
    var mark_after: List[List[Int]]
    var windows: List[List[Int]]
    var transitions: List[PrefixTransition]

    def __init__(out self, images: List[List[Int]], period: Int,
            generations: Int, seed: List[Int], word_cap: Int,
            occurrence_cap: Int, matrix: List[Int], block_images: List[List[Int]],
            block_matrix: List[Int]):
        self.images = images.copy()
        self.period = period
        self.generations = generations
        self.seed = seed.copy()
        self.word_cap = word_cap
        self.occurrence_cap = occurrence_cap
        self.matrix = matrix.copy()
        self.block_images = block_images.copy()
        self.block_matrix = block_matrix.copy()
        self.marks = List[List[Int]]()
        self.mark_before = List[List[Int]]()
        self.mark_after = List[List[Int]]()
        self.windows = List[List[Int]]()
        self.transitions = List[PrefixTransition]()


def _same_words(first: List[List[Int]], second: List[List[Int]]) -> Bool:
    if len(first) != len(second):
        return False
    for index in range(len(first)):
        if not same_vector(first[index],second[index]):
            return False
    return True


def _prefix_of(first: List[Int], second: List[Int]) -> Bool:
    if len(first) > len(second):
        return False
    for index in range(len(first)):
        if first[index] != second[index]:
            return False
    return True


def _word_slice(word: List[Int], start: Int, end: Int) raises -> List[Int]:
    if start < 0 or end < start or end > len(word):
        raise Error("prefix literal slice outside full word")
    var result = List[Int]()
    for index in range(start,end):
        result.append(word[index])
    return result^


def _triple(row: List[Int], offset: Int) -> List[Int]:
    return [row[offset],row[offset+1],row[offset+2]]


def _rows(matrix: List[Int]) raises -> List[List[Int]]:
    if len(matrix) != 9:
        raise Error("prefix incidence requires nine row-major entries")
    return [[matrix[0],matrix[1],matrix[2]],
            [matrix[3],matrix[4],matrix[5]],
            [matrix[6],matrix[7],matrix[8]]]


def _expanded_length(tau: Substitution, word: List[Int], cap: Int) raises -> Int:
    # Validate before indexing and refuse before materializing any oversized
    # complete word.  Every addition below is bounded above by cap <=4096.
    validate_word(word,3)
    var result = 0
    for letter in word:
        if len(tau.images[letter]) > cap-result:
            raise Error("complete prefix output window exceeds budget")
        result += len(tau.images[letter])
    return result


def build_prefix_closure(images: List[List[Int]], period: Int,
        seed: List[Int], generations: Int, word_cap: Int = PREFIX_WORD_CAP,
        occurrence_cap: Int = PREFIX_OCCURRENCE_CAP) raises -> PrefixClosure:
    """Construct complete windows for a productive prolonging seed.

    No incidence-injectivity or Pisot hypothesis is needed for these word
    identities.  Nonerasing plus strict prolongation is a sufficient finite
    input to the separate generic Lean limit theorem, not a finite check of
    an arbitrary right-infinite word.
    """
    if period < 1 or period > PREFIX_PERIOD_CAP:
        raise Error("prefix block period outside bounded range")
    if generations < 1 or generations > PREFIX_GENERATION_CAP:
        raise Error("prefix transition count outside bounded range")
    if word_cap < 1 or word_cap > PREFIX_WORD_CAP:
        raise Error("prefix complete-window budget outside bounded range")
    if occurrence_cap < 1 or occurrence_cap > PREFIX_OCCURRENCE_CAP:
        raise Error("prefix occurrence budget outside bounded range")
    if len(seed) < 1 or len(seed) > PREFIX_SEED_CAP or len(seed) > word_cap:
        raise Error("prefix seed length outside bounded range")
    var sigma = checked_substitution(images)
    validate_word(seed,3)
    # With three-letter images and period <=3 every full block has length
    # <=27.  The vendored power constructs literal images, not Parikh words.
    var tau = sigma.power(period)
    var matrix = sigma.incidence()
    var power: List[Int] = [1,0,0,0,1,0,0,0,1]
    for _ in range(period):
        power = matmul(power,matrix,3)
    if not same_vector(power,tau.incidence()):
        raise Error("literal block substitution disagrees with incidence power")
    var initial_length = _expanded_length(tau,seed,word_cap)
    var first = tau.apply(seed)
    if not _prefix_of(seed,first) or initial_length <= len(seed):
        raise Error("seed is not a strictly growing prolonging prefix")
    var certificate = PrefixClosure(images,period,generations,seed,word_cap,
        occurrence_cap,matrix,tau.images,power)
    var offsets: List[Int] = [0]
    for parent in range(3):
        ref word = tau.images[parent]
        for local in range(len(word)):
            var before = _word_slice(word,0,local)
            var after = _word_slice(word,local+1,len(word))
            var prefix = parikh(before)
            var suffix = parikh(after)
            certificate.marks.append([parent,local,word[local],prefix[0],prefix[1],
                prefix[2],suffix[0],suffix[1],suffix[2]])
            certificate.mark_before.append(before^)
            certificate.mark_after.append(after^)
        offsets.append(len(certificate.marks))
    certificate.windows.append(seed.copy())
    var total_occurrences = 0
    var power_rows = _rows(power)
    for generation in range(generations):
        var source = certificate.windows[generation].copy()
        var length = _expanded_length(tau,source,word_cap)
        if length > occurrence_cap-total_occurrences:
            raise Error("complete prefix occurrence inventory exceeds budget")
        var target = tau.apply(source)
        if len(target) != length or not _prefix_of(source,target) or length <= len(source):
            raise Error("productive prefix chain invariant failed")
        # This vendored routine cannot overflow after the complete length
        # preflight.  All N+1 boundaries, including the terminal one, survive.
        var boundaries = tau.image_prefix_lengths(source)
        var transition = PrefixTransition(generation)
        var source_prefix: List[Int] = [0,0,0]
        var target_prefix: List[Int] = [0,0,0]
        for parent_position in range(len(source)):
            var parent = source[parent_position]
            var transport = matvec(power_rows,source_prefix)
            if not same_vector(transport,target_prefix):
                raise Error("source-prefix incidence transport failed at cut")
            transition.cuts.append([parent_position,boundaries[parent_position],
                source_prefix[0],source_prefix[1],source_prefix[2],
                transport[0],transport[1],transport[2]])
            for local in range(len(tau.images[parent])):
                var mark_id = offsets[parent]+local
                ref mark = certificate.marks[mark_id]
                var global_position = boundaries[parent_position]+local
                var local_prefix = _triple(mark,3)
                var affine_prefix = add(transport,local_prefix)
                if global_position != len(transition.occurrences) or target[global_position] != mark[2]:
                    raise Error("literal prefix address coverage or selected letter failed")
                if not same_vector(affine_prefix,target_prefix):
                    raise Error("literal prefix Parikh identity failed")
                transition.occurrences.append([parent_position,parent,mark_id,local,
                    global_position,mark[2],source_prefix[0],source_prefix[1],source_prefix[2],
                    transport[0],transport[1],transport[2],local_prefix[0],local_prefix[1],
                    local_prefix[2],target_prefix[0],target_prefix[1],target_prefix[2]])
                # The complete bounded target makes these counts <=4096.
                target_prefix[mark[2]] += 1
            source_prefix[parent] += 1
        var terminal = matvec(power_rows,source_prefix)
        if len(transition.occurrences) != length or not same_vector(terminal,target_prefix):
            raise Error("complete prefix output or terminal transport missing")
        transition.cuts.append([len(source),length,source_prefix[0],source_prefix[1],
            source_prefix[2],terminal[0],terminal[1],terminal[2]])
        certificate.windows.append(target^)
        certificate.transitions.append(transition^)
        total_occurrences += length
    return certificate^


def verify_prefix_closure(certificate: PrefixClosure) raises:
    """Authenticate every submitted field against complete literal expansion."""
    var expected = build_prefix_closure(certificate.images,certificate.period,
        certificate.seed,certificate.generations,certificate.word_cap,certificate.occurrence_cap)
    if not same_vector(certificate.matrix,expected.matrix) or not same_vector(certificate.block_matrix,expected.block_matrix):
        raise Error("prefix certificate incidence or period scale changed")
    if not _same_words(certificate.block_images,expected.block_images):
        raise Error("prefix certificate literal block images changed")
    if not _same_words(certificate.marks,expected.marks) or not _same_words(certificate.mark_before,expected.mark_before) or not _same_words(certificate.mark_after,expected.mark_after):
        raise Error("prefix certificate complete local Mark inventory changed")
    if not _same_words(certificate.windows,expected.windows):
        raise Error("prefix certificate complete consecutive windows changed")
    if len(certificate.transitions) != len(expected.transitions):
        raise Error("prefix certificate omitted or repeated a transition")
    for generation in range(len(expected.transitions)):
        ref actual = certificate.transitions[generation]
        ref canonical = expected.transitions[generation]
        if actual.generation != generation or not _same_words(actual.cuts,canonical.cuts):
            raise Error("prefix certificate complete parent cuts changed")
        if not _same_words(actual.occurrences,canonical.occurrences):
            raise Error("prefix certificate literal occurrence inventory changed")


def bind_prefix_windows(images: List[List[Int]], period: Int, seed: List[Int],
        windows: List[List[Int]], word_cap: Int = PREFIX_WORD_CAP,
        occurrence_cap: Int = PREFIX_OCCURRENCE_CAP) raises -> PrefixClosure:
    """Refuse truncation, padding or skipped iterates in supplied whole windows."""
    if len(windows) < 2 or len(windows) > PREFIX_GENERATION_CAP+1:
        raise Error("prefix supplied window count outside bounded range")
    for window in windows:
        if len(window) > word_cap:
            raise Error("prefix supplied complete window exceeds budget")
        validate_word(window,3)
    var expected = build_prefix_closure(images,period,seed,len(windows)-1,word_cap,occurrence_cap)
    if not _same_words(windows,expected.windows):
        raise Error("supplied prefix windows are not the full consecutive expansion")
    return expected^


def lookup_prefix_address(certificate: PrefixClosure, generation: Int,
        global_position: Int) raises -> List[Int]:
    """Lookup on a constructed or separately verified certificate.

    The terminal cut is deliberately outside this selected-letter domain.
    """
    if generation < 0 or generation >= len(certificate.transitions) or generation+1 >= len(certificate.windows):
        raise Error("prefix lookup transition outside complete inventory")
    if global_position < 0 or global_position >= len(certificate.windows[generation+1]):
        raise Error("prefix lookup is not an actual output occurrence")
    ref occurrences = certificate.transitions[generation].occurrences
    if len(occurrences) != len(certificate.windows[generation+1]):
        raise Error("prefix lookup requires complete occurrence inventory")
    ref row = occurrences[global_position]
    if len(row) != 18 or row[4] != global_position:
        raise Error("prefix lookup occurrence identity changed")
    return row.copy()


def prefix_summary(certificate: PrefixClosure, generation: Int) raises -> List[Int]:
    if generation < 0 or generation >= len(certificate.transitions) or generation+1 >= len(certificate.windows):
        raise Error("prefix summary transition outside complete inventory")
    var source = parikh(certificate.windows[generation])
    var target = parikh(certificate.windows[generation+1])
    ref transition = certificate.transitions[generation]
    return [len(certificate.windows[generation]),len(certificate.windows[generation+1]),
        len(transition.cuts),len(transition.occurrences),source[0],source[1],source[2],
        target[0],target[1],target[2]]


def prefix_fixture(fixture: Int) raises -> PrefixClosure:
    if fixture < 0 or fixture > 3:
        raise Error("unknown prefix-closure fixture")
    var period = 2 if fixture < 2 else 1
    return build_prefix_closure(residue_fixture_images(fixture),period,[0],3)


def prefix_same_residue_control() raises -> List[Int]:
    """Different literal parent/global addresses can have identical residues."""
    var named = prefix_fixture(0)
    var first = lookup_prefix_address(named,2,0)
    var second = lookup_prefix_address(named,2,29)
    var residue = build_madic_residue(named.images,named.period)
    var first_class = residue_class(residue.levels[2],_triple(first,15))
    var second_class = residue_class(residue.levels[2],_triple(second,15))
    if first[0] == second[0] or first[4] == second[4] or first[2] != second[2] or first_class != second_class:
        raise Error("distinct-address same-residue control disappeared")
    return [0,2,2,first[4],second[4],first[0],second[0],first[3],second[3],first_class]


def prefix_refusal(control: Int) raises:
    """Each control must refuse the requested finite constructor or lookup."""
    var refused = False
    try:
        if control == 0:
            _ = build_prefix_closure([[],[],[]],1,[0],1)
        elif control == 1:
            _ = build_prefix_closure([[0,0],[],[2]],1,[0],1)
        elif control == 2:
            _ = build_prefix_closure([[0],[1],[2]],1,[0],1)
        elif control == 3:
            _ = build_prefix_closure([[1],[0],[2]],2,[0],1)
        elif control == 4:
            _ = build_prefix_closure(residue_fixture_images(0),1,[0],1)
        elif control == 5:
            _ = build_prefix_closure(residue_fixture_images(0),2,[],1)
        elif control == 6:
            _ = bind_prefix_windows(residue_fixture_images(0),2,[0],[[0],[0]])
        elif control == 7:
            _ = bind_prefix_windows(residue_fixture_images(0),2,[0],[[0],[0,2,1,0]])
        elif control == 8:
            _ = lookup_prefix_address(prefix_fixture(0),0,3)
        elif control == 9:
            _ = build_prefix_closure(residue_fixture_images(0),2,[0],3,word_cap=78)
        elif control == 10:
            _ = build_prefix_closure(residue_fixture_images(0),2,[0],3,occurrence_cap=96)
        elif control == 11:
            _ = build_prefix_closure(residue_fixture_images(0),4,[0],1)
        elif control == 12:
            _ = build_prefix_closure(residue_fixture_images(0),2,[0],4)
        elif control == 13:
            _ = bind_prefix_windows(residue_fixture_images(0),2,[0],[[0],[0,1,2]])
        else:
            raise Error("unknown prefix-closure refusal control")
    except:
        refused = True
    if control < 0 or control > 13 or not refused:
        raise Error("prefix-closure negative construction did not refuse")
