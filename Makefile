c0ll: bin
	lake build c0ll
	cp .lake/build/bin/c0ll bin/c0ll
	chmod +x bin/c0ll

bin:
	mkdir -p bin

clean:
	rm -rf bin
	lake clean

nocache:
	lake build --no-cache c0ll
	cp .lake/build/bin/c0ll bin/c0ll
	chmod +x bin/c0ll
