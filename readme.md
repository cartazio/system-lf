# modeling repo for linear logical system F
this repo is meant to exhibit the design and correctness notions for
a full intuitionistic / constructive embedding of linear logic in a functional setting.

# system linear f / linear system f is a mouthful, whats shorter
Sylph. Lets call this wee calculus sylph. Maybe lambda-something something later
who knows! Definitely not Lambda McLambdaFace.


# Where should i look for stuff?
most of the interesting code at the moment can be found in the ./model-agda relative directory

# why are there >=1 'model-foo' directory?
because different tools are good for different things, and some get tricky in
surprising ways.

Other developments will be included later for expository / etc reasons.

# whats the context of this project?
Sylph is meant to be a model calculus for the [Hopper language](http://github.com/hopper-language)
or something like that.

# why formalize things generally?
Describing anything complex is hard, having computers tell me i'm saying nonsense
is way faster than asking for fast refereeing or audits :)

# whats related work?
Well, types are calling conventions, along with many other functional programming
compilation research. Also a huge range of Linear logic ideas.


## whats an amusing fact about this project?
in the course of the modeling efforts a few amusing (but not deleterious) bugs in various
theorem provers have been found. All part of a days work to make the world a better place :)
