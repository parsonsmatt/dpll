# dpll

I'm lucky enough to get to use Haskell in my AI class.
I liked my implementation of the DPLL algorithm so well that I got permission to post it!
I tried a new (to me, in Haskell) methodology of writing a bunch of code at a fairly high level using intentionally abstract types/functions that didn't exist, and then defining them later on based on how I was using them.
It worked pretty well and the result was cool.

## The Code

The writeup that I turned in is in `dpll_writeup.lhs`, and a PDF/Latex render is in `dpll_writeup.pdf`.
The intended audience is my AI professor, who doesn't know Haskell, so some concepts might be blatantly obvious (like what `maybe` does) while some might be obtuse (what is the DPLL algorithm for anyway?).
I'm writing blog post aimed at Haskellers to accompany the code.
