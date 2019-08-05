FROM debian:buster-slim as builder
MAINTAINER LDL Tools development team <ldltools@outlook.com>

ENV DEBIAN_FRONTEND noninteractive
ENV DEBIAN_PRIORITY critical
ENV DEBCONF_NOWARNINGS yes

RUN echo "dash dash/sh boolean false" | debconf-set-selections;\
    dpkg-reconfigure -f noninteractive dash;\
    echo "/usr/local/lib" > /etc/ld.so.conf.d/usr-local-lib.conf;\
    apt-get update;\
    apt-get install -y build-essential flex bison gawk file rsync wget

# mona
RUN cd /root;\
    wget -q http://www.brics.dk/mona/download/mona-1.4-17.tar.gz;\
    tar xzf mona-1.4-17.tar.gz;\
    (cd mona-1.4; ./configure --prefix=/usr/local && make && make install-strip);\
    ldconfig

# opam2/ocaml
RUN apt-get install -y opam;\
    opam init -y --disable-sandboxing;\
    opam update;\
    opam switch create 4.08.0;\
    touch /root/.bash_profile && cat /root/.opam/opam-init/init.sh >> /root/.bash_profile

# ldlsat
ADD . /root/ldlsat
RUN cd /root/ldlsat;\
    eval `opam config env`;\
    opam install -y ocamlfind ppx_deriving ppx_deriving_yojson;\
    make veryclean && make && PREFIX=/usr/local make install

WORKDIR /root
CMD ["/bin/bash"]

# ====================
# final image
# ====================
FROM debian:buster-slim

RUN echo "dash dash/sh boolean false" | debconf-set-selections;\
    dpkg-reconfigure -f noninteractive dash;\
    echo "/usr/local/lib" > /etc/ld.so.conf.d/usr-local-lib.conf;\
    apt-get update;\
    apt-get install -y gawk

COPY --from=builder /usr/local /usr/local

WORKDIR /root
CMD ["/bin/bash"]
