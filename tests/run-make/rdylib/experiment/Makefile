all:
	rustc +stage1 libr.rs --emit=i-rs
	rustc +stage1 libr.rs
	rustc +stage1 app.rs -L.

clean:
	rm -f *.rdylib
	rm -f *.o
	rm -f *.txt
	rm -f *.rmeta
