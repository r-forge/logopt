\name{switching.portfolio}
\alias{switching.portfolio}
\title{ Portfolio selection using switching }
\description{
  Implement the portfolio selction defined by Singer.  The algorihtm is
  extremely simple but the function defined here is not able to exactly
  reproduce the published results for the adaptive version.
}
\usage{
switching.portfolio(x, gamma, method)
}
\arguments{
  \item{x}{
    Time series of relative prices
}
\item{gamma}{
  Parameter defining the switching rate
}
\item{method}{
  How the parameter gamma is controlled, "fixed" or "adaptive".
}
}
\details{
  Straightforward implementation of the switching portfolio
  algorithm.  The complexity of the "fixed" method is linear in the
  number of stocks and in the number of periods making it a very fast
  algorithm, but with a less favorable theoretical bound than Cover's
  Universal algorithm.  The "adaptive" method has a complexity linear
  in the square of periods, slower but still far from an exponential
  behavior.
}
\value{
  Return the time series of portfolio wealth.
}
\references{
  Yoram Singer, "Switching Portfolios", Int. J. Neural Syst. 1997,
  8(4): 445-55
}
\author{ Marc Delvaux
}

