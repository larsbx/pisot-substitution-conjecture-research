"""Export every literal incoming mark and normalized row slot for all 12 sources."""

from finite_exact.checked_int import checked_add
from psc.c4_literal_inverse_binding import build_literal_binding


def word_line(kind: String, source: Int, letter: Int, word: List[Int]) -> String:
    var line = kind+String(" ")+String(source)+String(" ")+String(letter)+String(" ")+String(len(word))
    for selected in word:
        line += String(" ")+String(selected)
    return line^


def main() raises:
    print("schema c4-literal-inverse-binding-v1")
    var total_states = 0
    var total_edges = 0
    var total_swapped = 0
    var total_repeated = 0
    var total_births = 0
    for source in range(12):
        var binding = build_literal_binding(source)
        var size = len(binding.graph.states)
        print("source",source,size,binding.edges)
        for letter in range(3):
            print(word_line("image",source,letter,binding.images[letter]))
        for letter in range(3):
            print(word_line("word",source,letter,binding.words[letter]))
        for i in range(len(binding.digits)):
            var d = binding.digits[i].copy()
            print("digit",source,i,d[0],d[1],d[2],d[3],d[4],d[5])
        for i in range(size):
            var state = binding.graph.states[i].copy()
            print("state",source,i,state[0],state[1],state[2],state[3],state[4])
        for i in range(size):
            for j in range(len(binding.slots[i])):
                var slot = binding.slots[i][j].copy()
                print("edge",source,i,j,slot[0],slot[1],slot[2],slot[3])
        for i in range(size):
            print("birth",source,i,binding.births[i][0],binding.births[i][1])
        print("summary",source,size,binding.edges,binding.swapped,binding.repeated,size-3)
        total_states = checked_add(total_states,size)
        total_edges = checked_add(total_edges,binding.edges)
        total_swapped = checked_add(total_swapped,binding.swapped)
        total_repeated = checked_add(total_repeated,binding.repeated)
        total_births = checked_add(total_births,size-3)
    print("total",12,total_states,total_edges,total_swapped,total_repeated,total_births)
