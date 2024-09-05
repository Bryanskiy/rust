all:
	rustc +stage1 libr.rs -C symbol-mangling-version=v0
	rustc +stage1 app.rs --extern lib=liblibr.rdylib -C symbol-mangling-version=v0

clean:
	rm -f *.rdylib
	find . -name "*._interface.rs" -type f -delete
	rm -f *.o
	rm -f *.txt
