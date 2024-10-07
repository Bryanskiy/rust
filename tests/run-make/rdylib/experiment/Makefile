all:
	rustc +stage1 libr.rs -C symbol-mangling-version=v0 --emit=i-rs
	rustc +stage1 app.rs -C symbol-mangling-version=v0 -L.

clean:
	rm -f *.rdylib
	find . -name "*._interface.rs" -type f -delete
	rm -f *.o
	rm -f *.txt
