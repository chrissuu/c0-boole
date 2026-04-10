# Running `make labN` should place an executable compiler at `bin/c0c`.
# Keep this interface for the 15-411 grading harness.

.PHONY: default lab% bin clean

default: lab3

lab%: bin
	lake build c0c
	cp .lake/build/bin/c0c bin/c0c
	chmod +x bin/c0c

bin:
	mkdir -p bin

clean:
	rm -rf bin
	lake clean

nocache:
	lake build --no-cache c0c
	cp .lake/build/bin/c0c bin/c0c
	chmod +x bin/c0c
