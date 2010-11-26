\name{bh}
\alias{bh}
\title{Buy and Hold portfolio}
\description{
  Calculate the time evolution of a Buy and Hold portfolio wealth given the prices relative and weights.
}
\usage{
bh(b = NULL, x)
}
\arguments{
  \item{b}{
    The portfolio weights with two variants: NULL or a vector.
    Null will be transformed as the uniform vector.
}
\item{x}{
          Time series of relative prices
}
}
\details{
  Calculate the time series of prices for the underlying assets, then calculate the wealth as a weighted sum of the individual assets.
}
\value{
    Time series of the wealth for the portfolio.
}
\author{ Marc Delvaux }