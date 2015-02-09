free env int(1, 2) xt;
env int(0, 2) yt;

assume active env proctype taz(){
    do
    :: yt = yt - 1
    :: yt = yt + 1
    :: skip
    od
}

assume ltl {
    []((xt != 1) || (yt != 2)) &&
    []<>(yt == 0) }

sys int(0, 3) x;
sys int(0, 2) y;

assert active sys proctype bunny(){
    do
    :: x = x - 1
    :: x = x + 1
    :: y = y - 1
    :: y = y + 1
    :: skip
    od
}

assert ltl {
    [] ! ((x == xt) && (y == yt)) &&
    []<>((x == 3) && (y == 1)) }
