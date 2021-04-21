
all: capp


usingcabal: ffisrc/Wrapper.hs wrapper.cabal.old
	rm wrapper.cabal
	cp wrapper.cabal.old wrapper.cabal
	cabal configure && cabal build
	find dist-newstyle/ -name 'libwrapper.*' -exec cp {} ./capp/ \;


wrapperlib: ffisrc/Wrapper.hs package.yaml stack.yaml
	# rm wrapper.cabal
	rm DiffPrivacyInferenceHs.cabal
	stack build
	find .stack-work/ -name 'libdiffmu-wrapper.*' -exec cp {} ./capp/ \;

capp: wrapperlib
	cd capp && make

run: capp
	cd capp && make run

clean:
	rm wrapper.cabal
	rm -r dist-newstyle
	stack clean && cd capp && make clean

.PHONY: all usingcabal wrapperlib capp run clean
